"""Telegram bot for escrow-based order flow between customers and executors.

The bot demonstrates the following business pipeline:
1) User chooses a role at first launch (customer or executor).
2) Customer creates and pays an order (funds go to escrow/deposit).
3) The order is broadcast to all executors.
4) Customer approves one of applicants.
5) Executor marks order as delivered and receives confirmation code by e-mail.
6) Executor forwards confirmation e-mail to bot's e-mail.
7) Bot validates the code from IMAP inbox and releases escrow to executor balance.
8) Confirmation codes are stored and checked for duplicates.
9) If confirmation deadline expires, escrow is refunded to customer.
"""

from __future__ import annotations

import asyncio
import imaplib
import os
import re
import secrets
import smtplib
import sqlite3
from contextlib import closing
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from email import message_from_bytes
from email.message import EmailMessage
from email.policy import default as email_default_policy
from pathlib import Path
from typing import Iterable

from aiogram import Bot, Dispatcher, F, Router
from aiogram.enums import ParseMode
from aiogram.filters import Command
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.types import InlineKeyboardButton, InlineKeyboardMarkup, Message, CallbackQuery
from dotenv import load_dotenv


# -------------------------------
# Configuration and constants
# -------------------------------
load_dotenv()

BOT_TOKEN = os.getenv("BOT_TOKEN", "")
BOT_EMAIL = os.getenv("BOT_EMAIL", "")
BOT_EMAIL_PASSWORD = os.getenv("BOT_EMAIL_PASSWORD", "")
IMAP_HOST = os.getenv("IMAP_HOST", "")
IMAP_PORT = int(os.getenv("IMAP_PORT", "993"))
SMTP_HOST = os.getenv("SMTP_HOST", "")
SMTP_PORT = int(os.getenv("SMTP_PORT", "465"))
DATABASE_PATH = os.getenv("DATABASE_PATH", "bot.db")
DEFAULT_CONFIRM_DEADLINE_HOURS = int(os.getenv("DEFAULT_CONFIRM_DEADLINE_HOURS", "24"))

if not BOT_TOKEN:
    raise RuntimeError("BOT_TOKEN is required. Fill .env first.")

CODE_REGEX = re.compile(r"CODE-(\d{6})")
ORDER_REGEX = re.compile(r"ORDER-(\d+)")


@dataclass
class User:
    id: int
    tg_id: int
    role: str
    balance: float
    email: str | None


class CreateOrderFSM(StatesGroup):
    title = State()
    description = State()
    amount = State()
    deadline_hours = State()
    ad_link = State()


# -------------------------------
# SQLite storage layer
# -------------------------------
class Storage:
    """Simple SQLite wrapper with explicit helper methods.

    We keep SQL as close as possible to business actions so the project
    stays easy to deploy on simple hosting (e.g., Beget shared plans).
    """

    def __init__(self, db_path: str) -> None:
        self.db_path = Path(db_path)
        self._init_schema()

    def _connect(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_path)
        conn.row_factory = sqlite3.Row
        return conn

    def _init_schema(self) -> None:
        with closing(self._connect()) as conn:
            conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS users (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    tg_id INTEGER UNIQUE NOT NULL,
                    role TEXT,
                    balance REAL NOT NULL DEFAULT 0,
                    email TEXT
                );

                CREATE TABLE IF NOT EXISTS orders (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    customer_tg_id INTEGER NOT NULL,
                    assigned_executor_tg_id INTEGER,
                    title TEXT NOT NULL,
                    description TEXT NOT NULL,
                    amount REAL NOT NULL,
                    ad_link TEXT,
                    status TEXT NOT NULL,
                    deadline_at TEXT NOT NULL,
                    confirm_code TEXT,
                    confirm_deadline_at TEXT,
                    created_at TEXT NOT NULL,
                    updated_at TEXT NOT NULL
                );

                CREATE TABLE IF NOT EXISTS order_responses (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    order_id INTEGER NOT NULL,
                    executor_tg_id INTEGER NOT NULL,
                    created_at TEXT NOT NULL,
                    UNIQUE(order_id, executor_tg_id)
                );

                CREATE TABLE IF NOT EXISTS used_confirmation_codes (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    code TEXT UNIQUE NOT NULL,
                    order_id INTEGER NOT NULL,
                    used_at TEXT NOT NULL
                );
                """
            )
            conn.commit()

    @staticmethod
    def now_iso() -> str:
        return datetime.now(timezone.utc).isoformat()

    def get_or_create_user(self, tg_id: int) -> sqlite3.Row:
        with closing(self._connect()) as conn:
            row = conn.execute("SELECT * FROM users WHERE tg_id = ?", (tg_id,)).fetchone()
            if row:
                return row
            conn.execute("INSERT INTO users (tg_id, role, balance) VALUES (?, NULL, 0)", (tg_id,))
            conn.commit()
            return conn.execute("SELECT * FROM users WHERE tg_id = ?", (tg_id,)).fetchone()

    def set_user_role(self, tg_id: int, role: str) -> None:
        with closing(self._connect()) as conn:
            conn.execute("UPDATE users SET role = ? WHERE tg_id = ?", (role, tg_id))
            conn.commit()

    def set_user_email(self, tg_id: int, email: str) -> None:
        with closing(self._connect()) as conn:
            conn.execute("UPDATE users SET email = ? WHERE tg_id = ?", (email, tg_id))
            conn.commit()

    def adjust_balance(self, tg_id: int, delta: float) -> None:
        with closing(self._connect()) as conn:
            conn.execute("UPDATE users SET balance = balance + ? WHERE tg_id = ?", (delta, tg_id))
            conn.commit()

    def get_user(self, tg_id: int) -> sqlite3.Row | None:
        with closing(self._connect()) as conn:
            return conn.execute("SELECT * FROM users WHERE tg_id = ?", (tg_id,)).fetchone()

    def list_executors(self) -> list[sqlite3.Row]:
        with closing(self._connect()) as conn:
            return conn.execute("SELECT * FROM users WHERE role = 'executor'").fetchall()

    def create_order(
        self,
        customer_tg_id: int,
        title: str,
        description: str,
        amount: float,
        deadline_hours: int,
        ad_link: str | None,
    ) -> int:
        now = self.now_iso()
        deadline = (datetime.now(timezone.utc) + timedelta(hours=deadline_hours)).isoformat()
        with closing(self._connect()) as conn:
            cur = conn.execute(
                """
                INSERT INTO orders (
                    customer_tg_id, title, description, amount, ad_link, status,
                    deadline_at, created_at, updated_at
                ) VALUES (?, ?, ?, ?, ?, 'open', ?, ?, ?)
                """,
                (customer_tg_id, title, description, amount, ad_link, deadline, now, now),
            )
            conn.commit()
            return int(cur.lastrowid)

    def list_open_orders_for_executor(self, executor_tg_id: int) -> list[sqlite3.Row]:
        with closing(self._connect()) as conn:
            return conn.execute(
                """
                SELECT * FROM orders
                WHERE status = 'open'
                  AND customer_tg_id != ?
                ORDER BY created_at DESC
                """,
                (executor_tg_id,),
            ).fetchall()

    def add_response(self, order_id: int, executor_tg_id: int) -> bool:
        with closing(self._connect()) as conn:
            try:
                conn.execute(
                    "INSERT INTO order_responses (order_id, executor_tg_id, created_at) VALUES (?, ?, ?)",
                    (order_id, executor_tg_id, self.now_iso()),
                )
                conn.commit()
                return True
            except sqlite3.IntegrityError:
                return False

    def list_order_responses(self, order_id: int) -> list[sqlite3.Row]:
        with closing(self._connect()) as conn:
            return conn.execute(
                "SELECT * FROM order_responses WHERE order_id = ? ORDER BY created_at ASC", (order_id,)
            ).fetchall()

    def assign_executor(self, order_id: int, executor_tg_id: int) -> None:
        with closing(self._connect()) as conn:
            conn.execute(
                "UPDATE orders SET assigned_executor_tg_id = ?, status = 'in_progress', updated_at = ? WHERE id = ?",
                (executor_tg_id, self.now_iso(), order_id),
            )
            conn.commit()

    def get_order(self, order_id: int) -> sqlite3.Row | None:
        with closing(self._connect()) as conn:
            return conn.execute("SELECT * FROM orders WHERE id = ?", (order_id,)).fetchone()

    def list_customer_orders(self, customer_tg_id: int) -> list[sqlite3.Row]:
        with closing(self._connect()) as conn:
            return conn.execute(
                "SELECT * FROM orders WHERE customer_tg_id = ? ORDER BY created_at DESC", (customer_tg_id,)
            ).fetchall()

    def list_executor_orders(self, executor_tg_id: int) -> list[sqlite3.Row]:
        with closing(self._connect()) as conn:
            return conn.execute(
                """
                SELECT * FROM orders
                WHERE assigned_executor_tg_id = ?
                  AND status IN ('in_progress', 'waiting_email_confirmation')
                ORDER BY created_at DESC
                """,
                (executor_tg_id,),
            ).fetchall()

    def mark_waiting_email_confirmation(self, order_id: int, code: str) -> str:
        confirm_deadline = (datetime.now(timezone.utc) + timedelta(hours=DEFAULT_CONFIRM_DEADLINE_HOURS)).isoformat()
        with closing(self._connect()) as conn:
            conn.execute(
                """
                UPDATE orders
                SET status = 'waiting_email_confirmation', confirm_code = ?, confirm_deadline_at = ?, updated_at = ?
                WHERE id = ?
                """,
                (code, confirm_deadline, self.now_iso(), order_id),
            )
            conn.commit()
        return confirm_deadline

    def is_code_used(self, code: str) -> bool:
        with closing(self._connect()) as conn:
            row = conn.execute("SELECT 1 FROM used_confirmation_codes WHERE code = ?", (code,)).fetchone()
            return row is not None

    def complete_order_with_code(self, order_id: int, code: str) -> None:
        with closing(self._connect()) as conn:
            conn.execute(
                "UPDATE orders SET status = 'completed', updated_at = ? WHERE id = ?",
                (self.now_iso(), order_id),
            )
            conn.execute(
                "INSERT INTO used_confirmation_codes (code, order_id, used_at) VALUES (?, ?, ?)",
                (code, order_id, self.now_iso()),
            )
            conn.commit()

    def list_expired_confirmation_orders(self) -> list[sqlite3.Row]:
        now = self.now_iso()
        with closing(self._connect()) as conn:
            return conn.execute(
                """
                SELECT * FROM orders
                WHERE status = 'waiting_email_confirmation'
                  AND confirm_deadline_at IS NOT NULL
                  AND confirm_deadline_at <= ?
                """,
                (now,),
            ).fetchall()

    def mark_order_refunded(self, order_id: int) -> None:
        with closing(self._connect()) as conn:
            conn.execute(
                "UPDATE orders SET status = 'refunded', updated_at = ? WHERE id = ?",
                (self.now_iso(), order_id),
            )
            conn.commit()


# -------------------------------
# E-mail helpers
# -------------------------------
def send_confirmation_email(to_email: str, order_id: int, code: str) -> None:
    """Send confirmation code to executor via SMTP."""
    msg = EmailMessage()
    msg["Subject"] = f"Код подтверждения для заказа ORDER-{order_id}"
    msg["From"] = BOT_EMAIL
    msg["To"] = to_email
    msg.set_content(
        "\n".join(
            [
                "Здравствуйте!",
                "Ниже код подтверждения для выплаты по заказу:",
                f"ORDER-{order_id}",
                f"CODE-{code}",
                "Перешлите это письмо на email бота для подтверждения выплаты.",
            ]
        )
    )

    with smtplib.SMTP_SSL(SMTP_HOST, SMTP_PORT, timeout=20) as smtp:
        smtp.login(BOT_EMAIL, BOT_EMAIL_PASSWORD)
        smtp.send_message(msg)


def fetch_confirmation_candidates(for_sender: str | None) -> list[tuple[int, str]]:
    """Read bot inbox and extract (order_id, code) from recent e-mails.

    If for_sender is passed, only e-mails from that sender are considered.
    """
    results: list[tuple[int, str]] = []
    with imaplib.IMAP4_SSL(IMAP_HOST, IMAP_PORT) as imap:
        imap.login(BOT_EMAIL, BOT_EMAIL_PASSWORD)
        imap.select("INBOX")
        criteria = '(UNSEEN SUBJECT "ORDER-")'
        status, data = imap.search(None, criteria)
        if status != "OK":
            return results

        for uid in data[0].split():
            status, msg_data = imap.fetch(uid, "(RFC822)")
            if status != "OK" or not msg_data or not msg_data[0]:
                continue

            raw_bytes = msg_data[0][1]
            parsed = message_from_bytes(raw_bytes, policy=email_default_policy)
            sender = (parsed.get("From") or "").lower()
            if for_sender and for_sender.lower() not in sender:
                continue

            body = parsed.get_body(preferencelist=("plain", "html"))
            text = body.get_content() if body else str(parsed)

            order_match = ORDER_REGEX.search(text)
            code_match = CODE_REGEX.search(text)
            if order_match and code_match:
                results.append((int(order_match.group(1)), code_match.group(1)))

    return results


# -------------------------------
# Bot UI helpers
# -------------------------------
def role_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="Заказчик", callback_data="set_role:customer")],
            [InlineKeyboardButton(text="Исполнитель", callback_data="set_role:executor")],
        ]
    )


def customer_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="➕ Создать заказ", callback_data="customer:create_order")],
            [InlineKeyboardButton(text="📦 Мои заказы", callback_data="customer:orders")],
            [InlineKeyboardButton(text="💳 Пополнить баланс +1000", callback_data="wallet:topup")],
            [InlineKeyboardButton(text="👛 Баланс", callback_data="wallet:show")],
        ]
    )


def executor_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🧾 Доступные заказы", callback_data="executor:open_orders")],
            [InlineKeyboardButton(text="📌 Мои активные заказы", callback_data="executor:my_orders")],
            [InlineKeyboardButton(text="📬 Проверить email подтверждение", callback_data="executor:check_email")],
            [InlineKeyboardButton(text="👛 Баланс", callback_data="wallet:show")],
        ]
    )


def order_status_ru(status: str) -> str:
    return {
        "open": "Открыт",
        "in_progress": "В работе",
        "waiting_email_confirmation": "Ожидает email-подтверждения",
        "completed": "Завершён",
        "refunded": "Возврат заказчику",
    }.get(status, status)


storage = Storage(DATABASE_PATH)
router = Router()


def format_order(order: sqlite3.Row) -> str:
    return (
        f"Заказ #{order['id']}\n"
        f"Название: {order['title']}\n"
        f"Описание: {order['description']}\n"
        f"Сумма: {order['amount']:.2f}\n"
        f"Статус: {order_status_ru(order['status'])}\n"
        f"Ссылка: {order['ad_link'] or 'не указана'}"
    )


@router.message(Command("start"))
async def cmd_start(message: Message) -> None:
    user = storage.get_or_create_user(message.from_user.id)
    if user["role"] is None:
        await message.answer("Добро пожаловать! Выберите ваш статус:", reply_markup=role_keyboard())
        return
    await show_menu(message, user["role"])


async def show_menu(message: Message, role: str) -> None:
    if role == "customer":
        await message.answer("Меню Заказчика:", reply_markup=customer_menu())
    elif role == "executor":
        await message.answer("Меню Исполнителя:", reply_markup=executor_menu())
    else:
        await message.answer("Роль не выбрана. Нажмите /start")


@router.message(Command("set_email"))
async def cmd_set_email(message: Message) -> None:
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) != 2 or "@" not in parts[1]:
        await message.answer("Использование: /set_email your@email.com")
        return
    storage.get_or_create_user(message.from_user.id)
    storage.set_user_email(message.from_user.id, parts[1].strip())
    await message.answer("Email сохранён. Теперь бот сможет отправлять код подтверждения.")


@router.callback_query(F.data.startswith("set_role:"))
async def cb_set_role(callback: CallbackQuery) -> None:
    role = callback.data.split(":", 1)[1]
    storage.set_user_role(callback.from_user.id, role)
    await callback.answer("Роль сохранена")
    await callback.message.answer(f"Вы выбрали: {'Заказчик' if role == 'customer' else 'Исполнитель'}")
    await show_menu(callback.message, role)


@router.callback_query(F.data == "wallet:show")
async def cb_wallet_show(callback: CallbackQuery) -> None:
    user = storage.get_or_create_user(callback.from_user.id)
    await callback.message.answer(f"Ваш баланс: {user['balance']:.2f}")
    await callback.answer()


@router.callback_query(F.data == "wallet:topup")
async def cb_wallet_topup(callback: CallbackQuery) -> None:
    storage.adjust_balance(callback.from_user.id, 1000)
    user = storage.get_user(callback.from_user.id)
    await callback.message.answer(f"Баланс пополнен на 1000. Текущий баланс: {user['balance']:.2f}")
    await callback.answer()


@router.callback_query(F.data == "customer:create_order")
async def cb_customer_create_order(callback: CallbackQuery, state: FSMContext) -> None:
    await state.set_state(CreateOrderFSM.title)
    await callback.message.answer("Введите название заказа:")
    await callback.answer()


@router.message(CreateOrderFSM.title)
async def fsm_order_title(message: Message, state: FSMContext) -> None:
    await state.update_data(title=message.text.strip())
    await state.set_state(CreateOrderFSM.description)
    await message.answer("Введите подробное описание заказа:")


@router.message(CreateOrderFSM.description)
async def fsm_order_description(message: Message, state: FSMContext) -> None:
    await state.update_data(description=message.text.strip())
    await state.set_state(CreateOrderFSM.amount)
    await message.answer("Введите сумму заказа (число):")


@router.message(CreateOrderFSM.amount)
async def fsm_order_amount(message: Message, state: FSMContext) -> None:
    try:
        amount = float(message.text.replace(",", "."))
        if amount <= 0:
            raise ValueError
    except Exception:
        await message.answer("Сумма должна быть положительным числом. Попробуйте снова:")
        return
    await state.update_data(amount=amount)
    await state.set_state(CreateOrderFSM.deadline_hours)
    await message.answer("Введите срок выполнения в часах (например, 48):")


@router.message(CreateOrderFSM.deadline_hours)
async def fsm_order_deadline(message: Message, state: FSMContext) -> None:
    try:
        hours = int(message.text)
        if hours <= 0:
            raise ValueError
    except Exception:
        await message.answer("Нужно целое положительное число часов. Попробуйте снова:")
        return

    await state.update_data(deadline_hours=hours)
    await state.set_state(CreateOrderFSM.ad_link)
    await message.answer("Введите ссылку на объявление (или '-' если нет):")


@router.message(CreateOrderFSM.ad_link)
async def fsm_order_finish(message: Message, state: FSMContext, bot: Bot) -> None:
    data = await state.get_data()
    ad_link = None if message.text.strip() == "-" else message.text.strip()
    user = storage.get_user(message.from_user.id)

    if user["balance"] < data["amount"]:
        await message.answer("Недостаточно средств. Пополните баланс и создайте заказ заново.")
        await state.clear()
        return

    # Reserve money on escrow: subtract from customer balance immediately.
    storage.adjust_balance(message.from_user.id, -data["amount"])
    order_id = storage.create_order(
        customer_tg_id=message.from_user.id,
        title=data["title"],
        description=data["description"],
        amount=data["amount"],
        deadline_hours=data["deadline_hours"],
        ad_link=ad_link,
    )
    await state.clear()

    await message.answer(
        f"Заказ #{order_id} создан и оплачен. Деньги зарезервированы на депозите.",
        reply_markup=customer_menu(),
    )

    # Broadcast to all executors.
    for executor in storage.list_executors():
        if executor["tg_id"] == message.from_user.id:
            continue
        kb = InlineKeyboardMarkup(
            inline_keyboard=[
                [
                    InlineKeyboardButton(
                        text="Откликнуться",
                        callback_data=f"executor:respond:{order_id}",
                    )
                ]
            ]
        )
        try:
            await bot.send_message(executor["tg_id"], f"Новый заказ!\n{format_order(storage.get_order(order_id))}", reply_markup=kb)
        except Exception:
            # Ignore dead chats / blocked bot to avoid crashing loop.
            pass


@router.callback_query(F.data == "customer:orders")
async def cb_customer_orders(callback: CallbackQuery) -> None:
    orders = storage.list_customer_orders(callback.from_user.id)
    if not orders:
        await callback.message.answer("У вас пока нет заказов.")
        await callback.answer()
        return

    for order in orders:
        responses = storage.list_order_responses(order["id"])
        text = format_order(order) + f"\nОткликов: {len(responses)}"
        await callback.message.answer(text)

        # For open orders with responses, customer can pick executor.
        if order["status"] == "open" and responses:
            buttons = [
                [
                    InlineKeyboardButton(
                        text=f"Утвердить исполнителя {resp['executor_tg_id']}",
                        callback_data=f"customer:approve:{order['id']}:{resp['executor_tg_id']}",
                    )
                ]
                for resp in responses
            ]
            await callback.message.answer("Выберите исполнителя:", reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))
    await callback.answer()


@router.callback_query(F.data.startswith("executor:respond:"))
async def cb_executor_respond(callback: CallbackQuery) -> None:
    order_id = int(callback.data.split(":")[-1])
    order = storage.get_order(order_id)
    if not order or order["status"] != "open":
        await callback.answer("Заказ уже неактуален", show_alert=True)
        return

    ok = storage.add_response(order_id, callback.from_user.id)
    if not ok:
        await callback.answer("Вы уже откликались на этот заказ")
        return

    await callback.answer("Отклик отправлен заказчику")


@router.callback_query(F.data.startswith("customer:approve:"))
async def cb_customer_approve(callback: CallbackQuery, bot: Bot) -> None:
    _, _, order_id_str, executor_tg_id_str = callback.data.split(":")
    order_id = int(order_id_str)
    executor_tg_id = int(executor_tg_id_str)
    order = storage.get_order(order_id)

    if not order or order["customer_tg_id"] != callback.from_user.id:
        await callback.answer("Недоступно", show_alert=True)
        return
    if order["status"] != "open":
        await callback.answer("Заказ уже обработан", show_alert=True)
        return

    storage.assign_executor(order_id, executor_tg_id)
    await callback.answer("Исполнитель утверждён")
    await callback.message.answer(f"Исполнитель {executor_tg_id} назначен на заказ #{order_id}.")

    deliver_kb = InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="Сдать заказ", callback_data=f"executor:deliver:{order_id}")]]
    )
    try:
        await bot.send_message(executor_tg_id, f"Вы назначены исполнителем на заказ #{order_id}.", reply_markup=deliver_kb)
    except Exception:
        pass


@router.callback_query(F.data == "executor:open_orders")
async def cb_executor_open_orders(callback: CallbackQuery) -> None:
    orders = storage.list_open_orders_for_executor(callback.from_user.id)
    if not orders:
        await callback.message.answer("Доступных заказов нет.")
        await callback.answer()
        return

    for order in orders:
        kb = InlineKeyboardMarkup(
            inline_keyboard=[
                [InlineKeyboardButton(text="Откликнуться", callback_data=f"executor:respond:{order['id']}")]
            ]
        )
        await callback.message.answer(format_order(order), reply_markup=kb)
    await callback.answer()


@router.callback_query(F.data == "executor:my_orders")
async def cb_executor_my_orders(callback: CallbackQuery) -> None:
    orders = storage.list_executor_orders(callback.from_user.id)
    if not orders:
        await callback.message.answer("У вас нет активных заказов.")
        await callback.answer()
        return

    for order in orders:
        buttons = []
        if order["status"] == "in_progress":
            buttons.append([InlineKeyboardButton(text="Сдать заказ", callback_data=f"executor:deliver:{order['id']}")])
        if order["status"] == "waiting_email_confirmation":
            buttons.append([InlineKeyboardButton(text="Проверить email", callback_data="executor:check_email")])
        kb = InlineKeyboardMarkup(inline_keyboard=buttons) if buttons else None
        await callback.message.answer(format_order(order), reply_markup=kb)
    await callback.answer()


@router.callback_query(F.data.startswith("executor:deliver:"))
async def cb_executor_deliver(callback: CallbackQuery) -> None:
    order_id = int(callback.data.split(":")[-1])
    order = storage.get_order(order_id)
    user = storage.get_user(callback.from_user.id)

    if not order or order["assigned_executor_tg_id"] != callback.from_user.id:
        await callback.answer("Это не ваш заказ", show_alert=True)
        return
    if order["status"] != "in_progress":
        await callback.answer("Заказ уже в другом статусе", show_alert=True)
        return
    if not user["email"]:
        await callback.message.answer("Сначала укажите email через команду /set_email your@email.com")
        await callback.answer()
        return

    code = f"{secrets.randbelow(900000) + 100000}"
    confirm_deadline = storage.mark_waiting_email_confirmation(order_id, code)

    try:
        send_confirmation_email(user["email"], order_id, code)
        await callback.message.answer(
            "Код подтверждения отправлен на ваш email. "
            f"Перешлите письмо на {BOT_EMAIL}, затем нажмите 'Проверить email подтверждение'. "
            f"Крайний срок подтверждения: {confirm_deadline}"
        )
    except Exception as exc:
        await callback.message.answer(f"Не удалось отправить email: {exc}")
    await callback.answer()


@router.callback_query(F.data == "executor:check_email")
async def cb_executor_check_email(callback: CallbackQuery, bot: Bot) -> None:
    user = storage.get_user(callback.from_user.id)
    if not user or not user["email"]:
        await callback.message.answer("Укажите email через /set_email")
        await callback.answer()
        return

    candidates = fetch_confirmation_candidates(user["email"])
    if not candidates:
        await callback.message.answer("Подходящих писем с кодом пока не найдено.")
        await callback.answer()
        return

    # Try every candidate until successful order completion.
    for order_id, code in candidates:
        order = storage.get_order(order_id)
        if not order:
            continue
        if order["assigned_executor_tg_id"] != callback.from_user.id:
            continue
        if order["status"] != "waiting_email_confirmation":
            continue
        if storage.is_code_used(code):
            continue
        if order["confirm_code"] != code:
            continue

        storage.complete_order_with_code(order_id, code)
        storage.adjust_balance(callback.from_user.id, order["amount"])

        await callback.message.answer(f"Проверка успешна! Вам начислено {order['amount']:.2f} за заказ #{order_id}.")
        try:
            await bot.send_message(
                order["customer_tg_id"],
                f"Заказ #{order_id} завершён. Ссылка на объявление: {order['ad_link'] or 'не указана'}",
            )
        except Exception:
            pass
        await callback.answer()
        return

    await callback.message.answer("Письма найдены, но валидный код не обнаружен (или код уже использован).")
    await callback.answer()


async def refund_expired_orders(bot: Bot) -> None:
    """Background task: return escrow to customer when confirmation expired."""
    while True:
        await asyncio.sleep(60)
        expired = storage.list_expired_confirmation_orders()
        for order in expired:
            storage.adjust_balance(order["customer_tg_id"], order["amount"])
            storage.mark_order_refunded(order["id"])
            try:
                await bot.send_message(
                    order["customer_tg_id"],
                    f"Срок подтверждения заказа #{order['id']} истёк. Деньги {order['amount']:.2f} возвращены на ваш баланс.",
                )
            except Exception:
                pass
            if order["assigned_executor_tg_id"]:
                try:
                    await bot.send_message(
                        order["assigned_executor_tg_id"],
                        f"Срок подтверждения по заказу #{order['id']} истёк. Выплата отменена.",
                    )
                except Exception:
                    pass


async def main() -> None:
    bot = Bot(BOT_TOKEN, parse_mode=ParseMode.HTML)
    dp = Dispatcher()
    dp.include_router(router)

    # Launch background escrow-refund worker.
    asyncio.create_task(refund_expired_orders(bot))
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
