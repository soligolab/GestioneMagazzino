# magazzino.py
from flask import Flask, render_template, redirect, url_for, request, jsonify, flash, send_file, session, send_from_directory
from flask_sqlalchemy import SQLAlchemy
from flask_login import (
    LoginManager,
    UserMixin,
    AnonymousUserMixin,
    login_user,
    login_required,
    logout_user,
    current_user,
)
from sqlalchemy import func, select, or_, text, case
from sqlalchemy.orm import selectinload
from datetime import datetime, timezone, timedelta
from typing import Optional
from itertools import islice
from functools import wraps
import re
from werkzeug.security import generate_password_hash, check_password_hash
import json
import os, io, csv
import shutil
import threading
import uuid
from werkzeug.utils import secure_filename

# ===================== DEFAULT ETICHETTE =====================
DEFAULT_LABEL_W_MM = 50
DEFAULT_LABEL_H_MM = 10
DEFAULT_MARG_TB_MM = 15
DEFAULT_MARG_LR_MM = 10
DEFAULT_GAP_MM     = 1
DEFAULT_LABEL_PADDING_MM = 1.5
DEFAULT_LABEL_QR_SIZE_MM = 9
DEFAULT_LABEL_QR_MARGIN_MM = 1
DEFAULT_LABEL_POSITION_WIDTH_MM = 12
DEFAULT_LABEL_POSITION_FONT_PT = 7.0
DEFAULT_DYMO_LABEL_W_MM = 50
DEFAULT_DYMO_LABEL_H_MM = 12
DEFAULT_DYMO_MARGIN_X_MM = 1.5
DEFAULT_DYMO_MARGIN_Y_MM = 1.5
DEFAULT_DYMO_FONT_NAME = "Helvetica"
DEFAULT_DYMO_FONT_SIZE_PT = 7.0
DEFAULT_DYMO_SHOW_CATEGORY = True
DEFAULT_DYMO_SHOW_SUBTYPE = True
DEFAULT_DYMO_SHOW_THREAD = True
DEFAULT_DYMO_SHOW_MEASURE = True
DEFAULT_DYMO_SHOW_MAIN = True
DEFAULT_DYMO_SHOW_MATERIAL = True
DEFAULT_DYMO_SHOW_POSITION = True
DEFAULT_CARD_W_MM = 61
DEFAULT_CARD_H_MM = 30
DEFAULT_CARD_MARGIN_TB_MM = 12
DEFAULT_CARD_MARGIN_LR_MM = 12
DEFAULT_CARD_GAP_MM = 6
DEFAULT_CARD_PADDING_MM = 5
DEFAULT_CARD_QR_SIZE_MM = 9
DEFAULT_CARD_QR_MARGIN_MM = 1
DEFAULT_CARD_POSITION_WIDTH_MM = 12
DEFAULT_CARD_POSITION_FONT_PT = 8.5
DEFAULT_CARD_GAP_H_MM = 6
DEFAULT_CARD_GAP_V_MM = 6
DEFAULT_ORIENTATION_LANDSCAPE = True
DEFAULT_CARD_ORIENTATION_LANDSCAPE = False
DEFAULT_LABEL_PAGE_FORMAT = "A4"
DEFAULT_CARD_PAGE_FORMAT = "A4"
DEFAULT_QR_DEFAULT = True
DEFAULT_QR_BASE_URL = None  # es. "https://magazzino.local"
DEFAULT_MQTT_HOST = "localhost"
DEFAULT_MQTT_PORT = 1883
DEFAULT_MQTT_TOPIC = "magazzino/slot"
DEFAULT_MQTT_QOS = 0
DEFAULT_MQTT_RETAIN = False

PAGE_FORMAT_OPTIONS = [
    ("A4", "A4"),
    ("A5", "A5"),
    ("A3", "A3"),
    ("LETTER", "Lettera"),
    ("LEGAL", "Legal"),
]
PAGE_FORMAT_KEYS = {key for key, _label in PAGE_FORMAT_OPTIONS}
PAGE_FORMAT_LABELS = {key: label for key, label in PAGE_FORMAT_OPTIONS}

def mm_to_pt(mm): return mm * 2.8346456693

def normalize_page_format(value: Optional[str], default: str) -> str:
    key = (value or "").strip().upper()
    if key in PAGE_FORMAT_KEYS:
        return key
    return default

def page_format_label(key: str) -> str:
    return PAGE_FORMAT_LABELS.get(key, key)

def page_size_for_format(format_key: str):
    from reportlab.lib.pagesizes import A3, A4, A5, LETTER, LEGAL
    formats = {
        "A3": A3,
        "A4": A4,
        "A5": A5,
        "LETTER": LETTER,
        "LEGAL": LEGAL,
    }
    return formats.get(format_key, A4)

def _safe_next_url(next_url: Optional[str]) -> Optional[str]:
    if not next_url:
        return None
    if not next_url.startswith("/"):
        return None
    if next_url.startswith("//") or "://" in next_url:
        return None
    return next_url

def _load_backup_state() -> dict:
    if not os.path.exists(BACKUP_STATE_PATH):
        return {}
    try:
        with open(BACKUP_STATE_PATH, "r", encoding="utf-8") as handle:
            return json.load(handle) or {}
    except (json.JSONDecodeError, OSError, ValueError):
        return {}

def _save_backup_state(state: dict) -> None:
    os.makedirs(app.instance_path, exist_ok=True)
    with open(BACKUP_STATE_PATH, "w", encoding="utf-8") as handle:
        json.dump(state, handle, ensure_ascii=False, indent=2)

def _list_backup_files() -> list[str]:
    if not os.path.exists(BACKUP_DIR):
        return []
    files = [
        os.path.join(BACKUP_DIR, name)
        for name in os.listdir(BACKUP_DIR)
        if name.startswith("magazzino_backup_") and name.endswith(".db")
    ]
    return sorted(files, key=lambda path: os.path.getmtime(path), reverse=True)

def _rotate_backups() -> None:
    backups = _list_backup_files()
    for path in backups[BACKUP_KEEP:]:
        try:
            os.remove(path)
        except OSError:
            continue

def _create_backup(reason: str) -> Optional[str]:
    if not os.path.exists(db_path):
        return None
    os.makedirs(BACKUP_DIR, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_name = f"magazzino_backup_{stamp}.db"
    backup_path = os.path.join(BACKUP_DIR, backup_name)
    with _BACKUP_LOCK:
        if not os.path.exists(db_path):
            return None
        shutil.copy2(db_path, backup_path)
        os.utime(backup_path, None)  # set mtime=now so rotation keeps this file
        _rotate_backups()
        state = _load_backup_state()
        state["last_backup_time"] = os.path.getmtime(backup_path)
        state["last_backup_date"] = datetime.now().date().isoformat()
        state["last_backup_reason"] = reason
        _save_backup_state(state)
    return backup_path

def run_startup_backup() -> Optional[str]:
    return _create_backup("startup")

def maybe_daily_backup() -> Optional[str]:
    if not os.path.exists(db_path):
        return None
    state = _load_backup_state()
    today = datetime.now().date().isoformat()
    if state.get("last_check_date") == today:
        return None
    state["last_check_date"] = today
    last_backup_time = float(state.get("last_backup_time") or 0)
    db_mtime = os.path.getmtime(db_path)
    _save_backup_state(state)
    if db_mtime <= last_backup_time:
        return None
    return _create_backup("daily")

# ===================== FLASK & DB =====================
app = Flask(__name__, instance_relative_config=True)
app.config['SECRET_KEY'] = "supersecret"
app.config["REMEMBER_COOKIE_DURATION"] = timedelta(days=30)
os.makedirs(app.instance_path, exist_ok=True)
db_path = os.path.join(app.instance_path, "magazzino.db")
app.config['SQLALCHEMY_DATABASE_URI'] = f"sqlite:///{db_path}"
app.config['SQLALCHEMY_TRACK_MODIFICATIONS'] = False
db = SQLAlchemy(app)
BACKUP_DIR = os.path.join(app.instance_path, "backups")
BACKUP_STATE_PATH = os.path.join(app.instance_path, "backup_state.json")
BACKUP_KEEP = int(os.getenv("MAGAZZINO_BACKUP_KEEP", "7"))
_BACKUP_LOCK = threading.Lock()
AVATAR_UPLOAD_DIR = os.path.join(app.instance_path, "uploads", "avatars")
AVATAR_ALLOWED_EXTS = {"png", "jpg", "jpeg", "webp"}
AVATAR_DICEBEAR_STYLE = "avataaars"
AVATAR_LIBRARY_SEEDS = [
    "Azzurro",
    "Bruno",
    "Cielo",
    "Dalia",
    "Elio",
    "Fiamma",
    "Gelsomino",
    "Iride",
    "Luna",
    "Miele",
    "Nerino",
    "Onda",
]

login_manager = LoginManager(app)
login_manager.login_view = "login"

@app.before_request
def _daily_backup_check():
    maybe_daily_backup()

# ===================== MODELS =====================
class User(UserMixin, db.Model):
    id = db.Column(db.Integer, primary_key=True)
    username = db.Column(db.String(50), unique=True, nullable=False)
    password = db.Column(db.String(128), nullable=False)
    first_name = db.Column(db.String(80), nullable=True)
    last_name = db.Column(db.String(80), nullable=True)
    email = db.Column(db.String(120), nullable=True)
    avatar_type = db.Column(db.String(20), nullable=True)
    avatar_value = db.Column(db.String(200), nullable=True)
    social_links = db.Column(db.Text, nullable=True)
    role_id = db.Column(db.Integer, db.ForeignKey("role.id"), nullable=True)
    role = db.relationship("Role", back_populates="users", lazy="joined")

    def set_password(self, raw_password: str) -> None:
        self.password = generate_password_hash(raw_password)

    def check_password(self, raw_password: str) -> bool:
        if not self.password:
            return False
        if self.password.startswith("pbkdf2:") or self.password.startswith("scrypt:"):
            return check_password_hash(self.password, raw_password)
        return self.password == raw_password

    def has_permission(self, permission_key: str) -> bool:
        if not self.role_id:
            return False
        role = getattr(self, "role", None)
        if role:
            return any(p.key == permission_key for p in role.permissions)
        return (
            db.session.query(Permission.id)
            .join(RolePermission, Permission.id == RolePermission.permission_id)
            .filter(RolePermission.role_id == self.role_id, Permission.key == permission_key)
            .first()
            is not None
        )

class AnonymousUser(AnonymousUserMixin):
    def has_permission(self, permission_key: str) -> bool:
        return False

login_manager.anonymous_user = AnonymousUser

class Role(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(50), unique=True, nullable=False)
    description = db.Column(db.String(200), nullable=True)
    is_system = db.Column(db.Boolean, nullable=False, default=False)
    permissions = db.relationship("Permission", secondary="role_permission", back_populates="roles")
    users = db.relationship("User", back_populates="role")

class Permission(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    key = db.Column(db.String(80), unique=True, nullable=False)
    label = db.Column(db.String(120), nullable=False)
    description = db.Column(db.String(200), nullable=True)
    is_system = db.Column(db.Boolean, nullable=False, default=False)
    roles = db.relationship("Role", secondary="role_permission", back_populates="permissions")

class RolePermission(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    role_id = db.Column(db.Integer, db.ForeignKey("role.id"), nullable=False)
    permission_id = db.Column(db.Integer, db.ForeignKey("permission.id"), nullable=False)
    __table_args__ = (db.UniqueConstraint("role_id", "permission_id", name="uq_role_permission"),)

class Settings(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    label_w_mm = db.Column(db.Float, nullable=False, default=DEFAULT_LABEL_W_MM)
    label_h_mm = db.Column(db.Float, nullable=False, default=DEFAULT_LABEL_H_MM)
    margin_tb_mm = db.Column(db.Float, nullable=False, default=DEFAULT_MARG_TB_MM)
    margin_lr_mm = db.Column(db.Float, nullable=False, default=DEFAULT_MARG_LR_MM)
    gap_mm = db.Column(db.Float, nullable=False, default=DEFAULT_GAP_MM)
    label_padding_mm = db.Column(db.Float, nullable=False, default=DEFAULT_LABEL_PADDING_MM)
    label_qr_size_mm = db.Column(db.Float, nullable=False, default=DEFAULT_LABEL_QR_SIZE_MM)
    label_qr_margin_mm = db.Column(db.Float, nullable=False, default=DEFAULT_LABEL_QR_MARGIN_MM)
    label_position_width_mm = db.Column(db.Float, nullable=False, default=DEFAULT_LABEL_POSITION_WIDTH_MM)
    label_position_font_pt = db.Column(db.Float, nullable=False, default=DEFAULT_LABEL_POSITION_FONT_PT)
    label_page_format = db.Column(db.String(10), nullable=False, default=DEFAULT_LABEL_PAGE_FORMAT)
    dymo_label_w_mm = db.Column(db.Float, nullable=False, default=DEFAULT_DYMO_LABEL_W_MM)
    dymo_label_h_mm = db.Column(db.Float, nullable=False, default=DEFAULT_DYMO_LABEL_H_MM)
    dymo_margin_x_mm = db.Column(db.Float, nullable=False, default=DEFAULT_DYMO_MARGIN_X_MM)
    dymo_margin_y_mm = db.Column(db.Float, nullable=False, default=DEFAULT_DYMO_MARGIN_Y_MM)
    dymo_font_name = db.Column(db.String(80), nullable=False, default=DEFAULT_DYMO_FONT_NAME)
    dymo_font_size_pt = db.Column(db.Float, nullable=False, default=DEFAULT_DYMO_FONT_SIZE_PT)
    dymo_show_category = db.Column(db.Boolean, nullable=False, default=DEFAULT_DYMO_SHOW_CATEGORY)
    dymo_show_subtype = db.Column(db.Boolean, nullable=False, default=DEFAULT_DYMO_SHOW_SUBTYPE)
    dymo_show_thread = db.Column(db.Boolean, nullable=False, default=DEFAULT_DYMO_SHOW_THREAD)
    dymo_show_measure = db.Column(db.Boolean, nullable=False, default=DEFAULT_DYMO_SHOW_MEASURE)
    dymo_show_main = db.Column(db.Boolean, nullable=False, default=DEFAULT_DYMO_SHOW_MAIN)
    dymo_show_material = db.Column(db.Boolean, nullable=False, default=DEFAULT_DYMO_SHOW_MATERIAL)
    dymo_show_position = db.Column(db.Boolean, nullable=False, default=DEFAULT_DYMO_SHOW_POSITION)
    card_w_mm = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_W_MM)
    card_h_mm = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_H_MM)
    card_margin_tb_mm = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_MARGIN_TB_MM)
    card_margin_lr_mm = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_MARGIN_LR_MM)
    card_gap_mm = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_GAP_MM)
    card_padding_mm = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_PADDING_MM)
    card_qr_size_mm = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_QR_SIZE_MM)
    card_qr_margin_mm = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_QR_MARGIN_MM)
    card_position_width_mm = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_POSITION_WIDTH_MM)
    card_position_font_pt = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_POSITION_FONT_PT)
    card_gap_h_mm = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_GAP_H_MM)
    card_gap_v_mm = db.Column(db.Float, nullable=False, default=DEFAULT_CARD_GAP_V_MM)
    card_page_format = db.Column(db.String(10), nullable=False, default=DEFAULT_CARD_PAGE_FORMAT)
    orientation_landscape = db.Column(db.Boolean, nullable=False, default=DEFAULT_ORIENTATION_LANDSCAPE)
    card_orientation_landscape = db.Column(db.Boolean, nullable=False, default=DEFAULT_CARD_ORIENTATION_LANDSCAPE)
    qr_default = db.Column(db.Boolean, nullable=False, default=DEFAULT_QR_DEFAULT)
    qr_base_url = db.Column(db.String(200), nullable=True)

class MqttSettings(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    enabled = db.Column(db.Boolean, nullable=False, default=False)
    host = db.Column(db.String(200), nullable=True)
    port = db.Column(db.Integer, nullable=False, default=DEFAULT_MQTT_PORT)
    username = db.Column(db.String(200), nullable=True)
    password = db.Column(db.String(200), nullable=True)
    topic = db.Column(db.String(200), nullable=True)
    qos = db.Column(db.Integer, nullable=False, default=DEFAULT_MQTT_QOS)
    retain = db.Column(db.Boolean, nullable=False, default=DEFAULT_MQTT_RETAIN)
    client_id = db.Column(db.String(120), nullable=True)
    include_cabinet_name = db.Column(db.Boolean, nullable=False, default=True)
    include_cabinet_id = db.Column(db.Boolean, nullable=False, default=True)
    include_location_name = db.Column(db.Boolean, nullable=False, default=True)
    include_location_id = db.Column(db.Boolean, nullable=False, default=False)
    include_row = db.Column(db.Boolean, nullable=False, default=True)
    include_col = db.Column(db.Boolean, nullable=False, default=True)
    include_slot_label = db.Column(db.Boolean, nullable=False, default=True)
    include_items = db.Column(db.Boolean, nullable=False, default=True)
    include_item_id = db.Column(db.Boolean, nullable=False, default=True)
    include_item_name = db.Column(db.Boolean, nullable=False, default=True)
    include_item_category = db.Column(db.Boolean, nullable=False, default=True)
    include_item_category_color = db.Column(db.Boolean, nullable=False, default=False)
    include_item_quantity = db.Column(db.Boolean, nullable=False, default=True)
    include_item_position = db.Column(db.Boolean, nullable=False, default=True)
    include_item_description = db.Column(db.Boolean, nullable=False, default=False)
    include_item_material = db.Column(db.Boolean, nullable=False, default=False)
    include_item_finish = db.Column(db.Boolean, nullable=False, default=False)
    include_empty = db.Column(db.Boolean, nullable=False, default=True)

class KatodoSettings(db.Model):
    id      = db.Column(db.Integer, primary_key=True)
    enabled = db.Column(db.Boolean, nullable=False, default=False)
    api_url = db.Column(db.String(300), nullable=True)
    api_key = db.Column(db.String(200), nullable=True)

class KatodoProduct(db.Model):
    __tablename__ = 'katodo_product'
    id                 = db.Column(db.Integer, primary_key=True)
    ps_id              = db.Column(db.Integer, unique=True, nullable=False, index=True)
    reference          = db.Column(db.String(100), nullable=True, index=True)
    supplier_reference = db.Column(db.String(100), nullable=True)
    name               = db.Column(db.String(512), nullable=True)
    description_short  = db.Column(db.Text, nullable=True)
    description        = db.Column(db.Text, nullable=True)
    manufacturer_name  = db.Column(db.String(200), nullable=True)
    category_name      = db.Column(db.String(200), nullable=True)
    price              = db.Column(db.Float, nullable=True)
    wholesale_price    = db.Column(db.Float, nullable=True)
    weight             = db.Column(db.Float, nullable=True)
    active             = db.Column(db.Boolean, nullable=True)
    quantity           = db.Column(db.Integer, nullable=True, default=0)
    ps_image_id        = db.Column(db.Integer, nullable=True)
    ps_date_add        = db.Column(db.DateTime, nullable=True)
    ps_date_upd        = db.Column(db.DateTime, nullable=True)
    synced_at          = db.Column(db.DateTime, nullable=True)

class Category(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(50), unique=True, nullable=False)
    color = db.Column(db.String(7), nullable=False, default="#000000")  # HEX
    main_measure_mode = db.Column(db.String(16), nullable=False, default="length")
    __table_args__ = (db.Index("ix_category_name", "name"),)

class Material(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(50), unique=True, nullable=False)
    __table_args__ = (db.Index("ix_material_name", "name"),)

class Finish(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(50), unique=True, nullable=False)
    __table_args__ = (db.Index("ix_finish_name", "name"),)

class ThreadStandard(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    code = db.Column(db.String(8), unique=True, nullable=False)
    label = db.Column(db.String(50), nullable=False)
    sort_order = db.Column(db.Integer, nullable=False, default=0)
    __table_args__ = (db.Index("ix_thread_standard_code", "code"),)

class ThreadSize(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    standard_id = db.Column(db.Integer, db.ForeignKey("thread_standard.id"), nullable=False)
    value = db.Column(db.String(32), nullable=False)
    sort_order = db.Column(db.Integer, nullable=False, default=0)
    __table_args__ = (
        db.UniqueConstraint('standard_id', 'value', name='uq_size_per_standard'),
        db.Index("ix_thread_size_standard_value", "standard_id", "value"),
    )
    standard = db.relationship("ThreadStandard")

class CustomField(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(80), unique=True, nullable=False)
    field_type = db.Column(db.String(16), nullable=False, default="text")
    options = db.Column(db.String(512), nullable=True)
    unit = db.Column(db.String(32), nullable=True)
    sort_order = db.Column(db.Integer, nullable=False, default=0)
    is_active = db.Column(db.Boolean, nullable=False, default=True)

class CategoryFieldSetting(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    category_id = db.Column(db.Integer, db.ForeignKey("category.id"), nullable=False)
    field_key = db.Column(db.String(64), nullable=False)
    is_enabled = db.Column(db.Boolean, nullable=False, default=True)
    __table_args__ = (
        db.UniqueConstraint('category_id', 'field_key', name='uq_field_per_category'),
        db.Index("ix_category_field_setting_category", "category_id"),
    )

class ItemCustomFieldValue(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    item_id = db.Column(db.Integer, db.ForeignKey("item.id"), nullable=False)
    field_id = db.Column(db.Integer, db.ForeignKey("custom_field.id"), nullable=False)
    value_text = db.Column(db.String(255), nullable=True)
    __table_args__ = (
        db.UniqueConstraint('item_id', 'field_id', name='uq_custom_field_value'),
        db.Index("ix_item_custom_field_value_item", "item_id"),
    )

class Subtype(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    category_id = db.Column(db.Integer, db.ForeignKey("category.id"), nullable=False)
    name = db.Column(db.String(80), nullable=False)
    __table_args__ = (
        db.UniqueConstraint('category_id', 'name', name='uq_subtype_per_category'),
        db.Index("ix_subtype_category", "category_id"),
    )

class Location(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(80), unique=True, nullable=False)  # solo nome
    __table_args__ = (db.Index("ix_location_name", "name"),)

class Cabinet(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    location_id = db.Column(db.Integer, db.ForeignKey("location.id"), nullable=False)
    name = db.Column(db.String(80), unique=True, nullable=False)  # univoco globale
    rows_max = db.Column(db.Integer, nullable=False, default=128)
    cols_max = db.Column(db.String(2), nullable=False, default="ZZ")  # A..Z, AA..ZZ
    compartments_per_slot = db.Column(db.Integer, nullable=False, default=6)
    __table_args__ = (db.Index("ix_cabinet_location", "location_id"),)

class Slot(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    cabinet_id = db.Column(db.Integer, db.ForeignKey("cabinet.id"), nullable=False)
    row_num = db.Column(db.Integer, nullable=False)         # 1..128
    col_code = db.Column(db.String(2), nullable=False)      # A..Z, AA..ZZ
    is_blocked = db.Column(db.Boolean, nullable=False, default=False)
    display_label_override = db.Column(db.String(80), nullable=True)
    print_label_override = db.Column(db.String(80), nullable=True)
    __table_args__ = (
        db.UniqueConstraint('cabinet_id', 'row_num', 'col_code', name='uq_slot_in_cabinet'),
        db.Index("ix_slot_cabinet_row_col", "cabinet_id", "row_num", "col_code"),
    )

class DrawerMerge(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    cabinet_id = db.Column(db.Integer, db.ForeignKey("cabinet.id"), nullable=False)
    row_start = db.Column(db.Integer, nullable=False)
    row_end = db.Column(db.Integer, nullable=False)
    col_start = db.Column(db.String(2), nullable=False)
    col_end = db.Column(db.String(2), nullable=False)
    __table_args__ = (db.Index("ix_drawer_merge_cabinet", "cabinet_id"),)

class Item(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    category_id = db.Column(db.Integer, db.ForeignKey("category.id"), nullable=False)
    subtype_id  = db.Column(db.Integer, db.ForeignKey("subtype.id"), nullable=True)
    name = db.Column(db.String(120), nullable=False, default="")  # auto-composizione
    description = db.Column(db.String(255), nullable=True)
    share_drawer = db.Column(db.Boolean, nullable=False, default=False)
    # filettatura / misura
    thread_standard = db.Column(db.String(8), nullable=True)  # M, UNC, UNF
    thread_size     = db.Column(db.String(32), nullable=True) # "M3", "1/4-20", ...
    # dimensioni principali
    inner_d_mm      = db.Column(db.Float, nullable=True)      # foro interno (rondelle)
    thickness_mm    = db.Column(db.Float, nullable=True)      # spessore (rondelle)
    length_mm       = db.Column(db.Float, nullable=True)      # lunghezza
    outer_d_mm      = db.Column(db.Float, nullable=True)      # Ø esterno
    # materiali/quantità
    material_id     = db.Column(db.Integer, db.ForeignKey("material.id"), nullable=True)
    finish_id       = db.Column(db.Integer, db.ForeignKey("finish.id"), nullable=True)
    quantity        = db.Column(db.Integer, nullable=False, default=0)
    updated_at      = db.Column(db.DateTime, nullable=False, default=datetime.utcnow, onupdate=datetime.utcnow)
    # flag etichetta
    label_show_category = db.Column(db.Boolean, nullable=False, default=True)
    label_show_subtype  = db.Column(db.Boolean, nullable=False, default=True)
    label_show_thread   = db.Column(db.Boolean, nullable=False, default=True)
    label_show_measure  = db.Column(db.Boolean, nullable=False, default=True)
    label_show_main     = db.Column(db.Boolean, nullable=False, default=True)
    label_show_material = db.Column(db.Boolean, nullable=False, default=True)

    category = db.relationship("Category")
    subtype  = db.relationship("Subtype")
    material = db.relationship("Material")
    finish   = db.relationship("Finish")
    __table_args__ = (
        db.Index("ix_item_category", "category_id"),
        db.Index("ix_item_subtype", "subtype_id"),
        db.Index("ix_item_material", "material_id"),
        db.Index("ix_item_finish", "finish_id"),
        db.Index("ix_item_thread_size", "thread_size"),
        db.Index("ix_item_updated_at", "updated_at"),
    )

class Assignment(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    slot_id = db.Column(db.Integer, db.ForeignKey("slot.id"), nullable=False)
    compartment_no = db.Column(db.Integer, nullable=False, default=1)
    item_id = db.Column(db.Integer, db.ForeignKey("item.id"), nullable=False)
    __table_args__ = (
        db.Index("ix_assignment_item", "item_id"),
        db.Index("ix_assignment_slot", "slot_id"),
    )
    __table_args__ = (db.UniqueConstraint('slot_id', 'compartment_no', name='uq_compartment_in_slot'),)

# ===================== HELPERS =====================
def column_code_valid(code: str) -> bool:
    if not code: return False
    code = code.strip().upper()
    if len(code) == 1:   return 'A' <= code <= 'Z'
    if len(code) == 2:   return 'A' <= code[0] <= 'Z' and 'A' <= code[1] <= 'Z'
    return False

def users_with_permission(permission_key: str):
    return (User.query.join(Role)
            .join(RolePermission, Role.id == RolePermission.role_id)
            .join(Permission, Permission.id == RolePermission.permission_id)
            .filter(Permission.key == permission_key))

def colcode_to_idx(code:str)->int:
    code = code.strip().upper()
    if len(code)==1: return ord(code)-64
    if len(code)==2:
        first = ord(code[0]) - 65
        second = ord(code[1]) - 64
        return 26 + first*26 + second
    return 0

def idx_to_colcode(idx:int)->str:
    if idx<=26: return chr(64+idx)
    rem = idx - 26
    first = (rem-1)//26
    second = (rem-1)%26 + 1
    return chr(65+first) + chr(64+second)

def iter_cols_upto(max_code:str):
    max_i = colcode_to_idx(max_code)
    max_i = max(1, min(max_i, 702))
    for i in range(1, max_i+1):
        yield idx_to_colcode(i)

def normalize_merge_bounds(cab: Cabinet, col_start: str, col_end: str, row_start: int, row_end: int):
    if not (column_code_valid(col_start) and column_code_valid(col_end)):
        raise ValueError("Colonna non valida (A..Z o AA..ZZ).")
    if not (1 <= int(row_start) <= 128 and 1 <= int(row_end) <= 128):
        raise ValueError("Riga non valida (1..128).")
    max_col_idx = colcode_to_idx(cab.cols_max or "Z")
    c_start_idx = colcode_to_idx(col_start)
    c_end_idx = colcode_to_idx(col_end)
    if c_start_idx == 0 or c_end_idx == 0:
        raise ValueError("Colonna non valida (A..Z o AA..ZZ).")
    if c_start_idx > c_end_idx:
        c_start_idx, c_end_idx = c_end_idx, c_start_idx
    if row_start > row_end:
        row_start, row_end = row_end, row_start
    if row_start < 1 or row_end > cab.rows_max:
        raise ValueError("Righe fuori dai limiti della cassettiera.")
    if c_start_idx < 1 or c_end_idx > max_col_idx:
        raise ValueError("Colonne fuori dai limiti della cassettiera.")
    if row_start == row_end and c_start_idx == c_end_idx:
        raise ValueError("Seleziona almeno due celle adiacenti.")
    return row_start, row_end, idx_to_colcode(c_start_idx), idx_to_colcode(c_end_idx)

def merge_region_for(cabinet_id: int, col_code: str, row_num: int):
    merges = DrawerMerge.query.filter_by(cabinet_id=cabinet_id).all()
    if not merges:
        return None
    col_idx = colcode_to_idx(col_code)
    for m in merges:
        start_idx = colcode_to_idx(m.col_start)
        end_idx = colcode_to_idx(m.col_end)
        if start_idx > end_idx:
            start_idx, end_idx = end_idx, start_idx
        row_start = min(m.row_start, m.row_end)
        row_end = max(m.row_start, m.row_end)
        if start_idx <= col_idx <= end_idx and row_start <= row_num <= row_end:
            return {
                "anchor_col": idx_to_colcode(start_idx),
                "anchor_row": row_start,
                "row_start": row_start,
                "row_end": row_end,
                "col_start": idx_to_colcode(start_idx),
                "col_end": idx_to_colcode(end_idx),
            }
    return None

def merge_cells_from_region(region):
    if not region:
        return []
    start_idx = colcode_to_idx(region["col_start"])
    end_idx = colcode_to_idx(region["col_end"])
    cells = []
    for row in range(region["row_start"], region["row_end"] + 1):
        for col_idx in range(start_idx, end_idx + 1):
            cells.append((idx_to_colcode(col_idx), row))
    return cells


def _merged_cell_multiplier(cabinet: Cabinet | None, col_code: str, row_num: int) -> int:
    if not cabinet:
        return 1
    region = merge_region_for(cabinet.id, col_code, row_num)
    if not region:
        return 1
    start_idx = colcode_to_idx(region["col_start"])
    end_idx = colcode_to_idx(region["col_end"])
    cols = max(1, end_idx - start_idx + 1)
    rows = max(1, region["row_end"] - region["row_start"] + 1)
    return cols * rows


def _max_compartments_for_slot(cabinet: Cabinet | None, col_code: str, row_num: int) -> int:
    base = cabinet.compartments_per_slot if cabinet else None
    base = base or 6
    multiplier = _merged_cell_multiplier(cabinet, col_code, row_num)
    return max(1, int(base)) * max(1, multiplier)


def _collect_region_assignments(cabinet_id: int, col_code: str, row_num: int, *, ignore_item_id: int | None = None):
    """
    Raccoglie slot e assegnamenti per la cella indicata, includendo tutte le celle fuse.
    Restituisce (anchor_slot, all_slots, assignments, items).
    """
    region = merge_region_for(cabinet_id, col_code, row_num)
    anchor_col = col_code
    anchor_row = row_num
    cells = [(col_code, row_num)]
    if region:
        anchor_col = region["anchor_col"]
        anchor_row = region["anchor_row"]
        cells = merge_cells_from_region(region)

    # Assicura che esista lo slot anchor
    anchor_slot = _ensure_slot(cabinet_id, anchor_col, anchor_row)
    slots = []
    assignments = []
    items = []
    for col, row in cells:
        slot = _ensure_slot(cabinet_id, col, row)
        slots.append(slot)
        assigns, slot_items = _load_slot_assignments(slot.id, ignore_item_id=ignore_item_id)
        assignments.extend(assigns)
        items.extend(slot_items)

    return anchor_slot, slots, assignments, items

def make_full_position(cab_name: str, col_code: str, row_num: int, label_override: str | None = None) -> str:
    base_label = (label_override or f"{col_code.upper()}{int(row_num)}").strip()
    return f"{cab_name}-{base_label}" if cab_name else base_label

def slot_label(slot: Slot | None, *, for_display: bool = True, fallback_col: str | None = None, fallback_row: int | None = None) -> str:
    if slot:
        override = slot.display_label_override if for_display else slot.print_label_override
        col = slot.col_code
        row = slot.row_num
    else:
        override = None
        col = fallback_col
        row = fallback_row
    base = f"{(col or '').upper()}{int(row) if row is not None else ''}".strip()
    if override:
        cleaned = override.strip()
        if cleaned:
            return cleaned
    return base

def slot_full_label(cabinet: Cabinet | None, slot: Slot | None, *, for_print: bool = False, fallback_col: str | None = None, fallback_row: int | None = None) -> str:
    base = slot_label(slot, for_display=not for_print, fallback_col=fallback_col, fallback_row=fallback_row)
    if cabinet and cabinet.name:
        return f"{cabinet.name}-{base}"
    return base

CATEGORY_ROLE_ALIASES = {
    "washer": ["rondelle"],
    "screw": ["viti"],
    "standoff": ["torrette"],
    "spacer": ["distanziali"],
}

_CATEGORY_ROLE_IDS = {}


def _normalize_name(value: Optional[str]) -> str:
    return (value or "").strip().lower()


def _category_role_id(role: str) -> Optional[int]:
    cid = _CATEGORY_ROLE_IDS.get(role)
    if cid:
        return cid

    aliases = CATEGORY_ROLE_ALIASES.get(role, [])
    if not aliases:
        return None

    name_to_id = {
        _normalize_name(name): cid
        for cid, name in Category.query.with_entities(Category.id, Category.name)
    }
    for alias in aliases:
        cid = name_to_id.get(_normalize_name(alias))
        if cid:
            _CATEGORY_ROLE_IDS[role] = cid
            return cid
    return None


def reset_category_role_cache() -> None:
    _CATEGORY_ROLE_IDS.clear()


def is_washer(item: Item) -> bool:
    cat_id = _category_role_id("washer")
    return bool(cat_id and item.category_id == cat_id)


def is_screw(item: Item) -> bool:
    cat_id = _category_role_id("screw")
    return bool(cat_id and item.category_id == cat_id)


def is_standoff(item: Item) -> bool:
    cat_id = _category_role_id("standoff")
    return bool(cat_id and item.category_id == cat_id)


def is_spacer(item: Item) -> bool:
    cat_id = _category_role_id("spacer")
    return bool(cat_id and item.category_id == cat_id)

def auto_name_for(item:Item)->str:
    parts=[]
    if item.category: parts.append(item.category.name)
    if item.subtype: parts.append(item.subtype.name)  # forma testa / forma torrette
    if item.thread_size: parts.append(item.thread_size)
    size_value = None
    tag = None
    if is_screw(item) or is_standoff(item) or is_spacer(item):
        size_value = item.length_mm
        tag = "L="
    else:
        size_value = item.outer_d_mm
        tag = "Øe"
    if size_value is not None:
        val = int(size_value) if float(size_value).is_integer() else size_value
        parts.append(f"{tag}{val}mm")
    if item.material: parts.append(item.material.name)
    return " ".join(parts)[:118]

def _name_tokens(value: str) -> list[str]:
    cleaned = (value or "").strip()
    if not cleaned:
        return []
    tokens = re.split(r"\s+", cleaned)
    out = []
    for token in tokens:
        token = re.sub(r"^[^\wØø]+|[^\wØø]+$", "", token, flags=re.UNICODE)
        if token:
            out.append(token)
    return out

def shared_drawer_label(items: list[Item]) -> str | None:
    if not items or len(items) < 2:
        return None
    names = []
    for it in items:
        base = (it.name or "").strip()
        if not base:
            base = auto_name_for(it)
        if base:
            names.append(base)
    if len(names) < 2:
        return None
    first_tokens = _name_tokens(names[0])
    if not first_tokens:
        return None
    other_sets = [set(t.lower() for t in _name_tokens(name)) for name in names[1:]]
    if not other_sets:
        return None
    common = []
    for token in first_tokens:
        token_key = token.lower()
        if all(token_key in tokens for tokens in other_sets):
            common.append(token)
    if not common:
        return None
    return " ".join(common)[:80]

def format_mm_short(value):
    """Restituisce un valore in mm come intero se possibile o con una singola cifra decimale."""
    if value is None:
        return None
    try:
        v = float(value)
    except (TypeError, ValueError):
        return None
    if abs(v - round(v)) < 0.01:
        return str(int(round(v)))
    return f"{v:.1f}".rstrip("0").rstrip(".")

MAIN_MEASURE_DEFAULT = "length"
VALID_MEASURE_MODES = {"length", "thickness"}
LENGTH_ABBR = "Lun."
THICKNESS_ABBR = "Spess."


def measure_mode_for_category(cat: Category | None) -> str:
    mode = getattr(cat, "main_measure_mode", None) or MAIN_MEASURE_DEFAULT
    return mode if mode in VALID_MEASURE_MODES else MAIN_MEASURE_DEFAULT


def measure_label_for_mode(mode: str, include_units: bool = True) -> str:
    base = "Spessore" if mode == "thickness" else "Lunghezza"
    return f"{base} (mm)" if include_units else base


def measure_label_for_category(cat: Category | None, include_units: bool = True) -> str:
    return measure_label_for_mode(measure_mode_for_category(cat), include_units)


def main_measure_value(item: Item | None):
    if not item:
        return None
    mode = measure_mode_for_category(item.category)
    if mode == "thickness":
        return item.thickness_mm if item.thickness_mm is not None else item.length_mm
    return item.length_mm if item.length_mm is not None else item.thickness_mm


def formatted_main_measure(item: Item | None) -> str | None:
    return format_mm_short(main_measure_value(item))


def main_measure_info(item: Item) -> dict | None:
    value = formatted_main_measure(item)
    if not value:
        return None
    mode = measure_mode_for_category(item.category)
    return {
        "mode": mode,
        "value": value,
        "label": measure_label_for_mode(mode, include_units=False),
    }


def build_measure_labels(categories):
    return {c.id: measure_label_for_category(c) for c in categories}

def label_line1_text(item: Item) -> str:
    """Testo riga 1 dell'etichetta: Categoria + Sottotipo + Misura filettatura."""
    parts = []
    if item.category:
        parts.append(item.category.name)
    if item.subtype:
        parts.append(item.subtype.name)
    if item.thread_size:
        parts.append(item.thread_size)
    return " ".join(parts)

def label_line2_text(item: Item) -> str:
    """Testo riga 2 dell'etichetta: dati tecnici a seconda della categoria."""
    parts = []

    if is_screw(item):
        v = format_mm_short(item.length_mm)
        if v:
            parts.append(f"{LENGTH_ABBR} {v}")
        if item.material:
            parts.append(item.material.name)
    elif is_washer(item):
        v_i = format_mm_short(getattr(item, "inner_d_mm", None))
        if v_i:
            parts.append(f"Øi{v_i}")
        v_e = format_mm_short(item.outer_d_mm)
        if v_e:
            parts.append(f"Øe{v_e}")
        v_s_raw = unified_thickness_value(item)
        v_s = format_mm_short(v_s_raw)
        if v_s:
            prefix = THICKNESS_ABBR if item.thickness_mm is not None else LENGTH_ABBR
            parts.append(f"{prefix} {v_s}")
    elif is_standoff(item):
        v = format_mm_short(item.length_mm)
        if v:
            parts.append(f"{LENGTH_ABBR} {v}")
        if item.material:
            parts.append(item.material.name)
    else:
        v = format_mm_short(item.outer_d_mm)
        if v:
            parts.append(f"Øe{v}")
        v_s_raw = unified_thickness_value(item)
        v_s = format_mm_short(v_s_raw)
        if v_s:
            prefix = THICKNESS_ABBR if item.thickness_mm is not None else LENGTH_ABBR
            parts.append(f"{prefix} {v_s}")
        if item.material:
            parts.append(item.material.name)

    return " ".join(parts)

def label_lines_for_item(item: Item) -> list[str]:
    """Restituisce le righe di testo da mostrare in cella e in etichetta."""
    lines = []
    line1 = label_line1_text(item)
    line2 = label_line2_text(item)
    if line1:
        lines.append(line1)
    if line2:
        lines.append(line2)
    if not lines:
        fallback = auto_name_for(item)
        if fallback:
            lines.append(fallback)
    return lines

def dymo_label_lines(item: Item, settings: Settings, position_label: str | None) -> list[str]:
    lines = []
    line1_parts = []
    if settings.dymo_show_category and item.label_show_category and item.category:
        line1_parts.append(item.category.name)
    if settings.dymo_show_subtype and item.label_show_subtype and item.subtype:
        line1_parts.append(item.subtype.name)
    if settings.dymo_show_thread and item.label_show_thread and item.thread_size:
        line1_parts.append(item.thread_size)
    if line1_parts:
        lines.append(" ".join(line1_parts))

    detail_parts = []
    if is_screw(item):
        if settings.dymo_show_main and item.label_show_main:
            v = format_mm_short(item.length_mm)
            if v:
                detail_parts.append(f"{LENGTH_ABBR} {v}")
        if settings.dymo_show_material and item.label_show_material and item.material:
            detail_parts.append(item.material.name)
    elif is_washer(item):
        if settings.dymo_show_measure and item.label_show_measure:
            v_i = format_mm_short(getattr(item, "inner_d_mm", None))
            if v_i:
                detail_parts.append(f"Øi{v_i}")
        if settings.dymo_show_main and item.label_show_main:
            v_e = format_mm_short(item.outer_d_mm)
            if v_e:
                detail_parts.append(f"Øe{v_e}")
            v_s_raw = unified_thickness_value(item)
            v_s = format_mm_short(v_s_raw)
            if v_s:
                prefix = THICKNESS_ABBR if item.thickness_mm is not None else LENGTH_ABBR
                detail_parts.append(f"{prefix} {v_s}")
        if settings.dymo_show_material and item.label_show_material and item.material:
            detail_parts.append(item.material.name)
    elif is_standoff(item):
        if settings.dymo_show_main and item.label_show_main:
            v = format_mm_short(item.length_mm)
            if v:
                detail_parts.append(f"{LENGTH_ABBR} {v}")
        if settings.dymo_show_material and item.label_show_material and item.material:
            detail_parts.append(item.material.name)
    else:
        if settings.dymo_show_main and item.label_show_main:
            v = format_mm_short(item.outer_d_mm)
            if v:
                detail_parts.append(f"Øe{v}")
            v_s_raw = unified_thickness_value(item)
            v_s = format_mm_short(v_s_raw)
            if v_s:
                prefix = THICKNESS_ABBR if item.thickness_mm is not None else LENGTH_ABBR
                detail_parts.append(f"{prefix} {v_s}")
        if settings.dymo_show_material and item.label_show_material and item.material:
            detail_parts.append(item.material.name)
    if detail_parts:
        lines.append(" ".join(detail_parts))

    if settings.dymo_show_position and position_label:
        lines.append(position_label)

    if not lines:
        fallback = item.name or auto_name_for(item)
        if fallback:
            lines.append(fallback)
    return lines

def ensure_settings_columns():
    """Aggiunge le nuove colonne delle impostazioni se mancano nel DB SQLite."""
    try:
        rows = db.session.execute(text("PRAGMA table_info(settings)")).fetchall()
    except Exception:
        return
    existing_cols = {r[1] for r in rows}
    new_cols = [
        ("label_padding_mm", "REAL", DEFAULT_LABEL_PADDING_MM),
        ("label_qr_size_mm", "REAL", DEFAULT_LABEL_QR_SIZE_MM),
        ("label_qr_margin_mm", "REAL", DEFAULT_LABEL_QR_MARGIN_MM),
        ("label_position_width_mm", "REAL", DEFAULT_LABEL_POSITION_WIDTH_MM),
        ("label_position_font_pt", "REAL", DEFAULT_LABEL_POSITION_FONT_PT),
        ("label_page_format", "VARCHAR(10)", DEFAULT_LABEL_PAGE_FORMAT),
        ("dymo_label_w_mm", "REAL", DEFAULT_DYMO_LABEL_W_MM),
        ("dymo_label_h_mm", "REAL", DEFAULT_DYMO_LABEL_H_MM),
        ("dymo_margin_x_mm", "REAL", DEFAULT_DYMO_MARGIN_X_MM),
        ("dymo_margin_y_mm", "REAL", DEFAULT_DYMO_MARGIN_Y_MM),
        ("dymo_font_name", "VARCHAR(80)", DEFAULT_DYMO_FONT_NAME),
        ("dymo_font_size_pt", "REAL", DEFAULT_DYMO_FONT_SIZE_PT),
        ("dymo_show_category", "BOOLEAN", int(DEFAULT_DYMO_SHOW_CATEGORY)),
        ("dymo_show_subtype", "BOOLEAN", int(DEFAULT_DYMO_SHOW_SUBTYPE)),
        ("dymo_show_thread", "BOOLEAN", int(DEFAULT_DYMO_SHOW_THREAD)),
        ("dymo_show_measure", "BOOLEAN", int(DEFAULT_DYMO_SHOW_MEASURE)),
        ("dymo_show_main", "BOOLEAN", int(DEFAULT_DYMO_SHOW_MAIN)),
        ("dymo_show_material", "BOOLEAN", int(DEFAULT_DYMO_SHOW_MATERIAL)),
        ("dymo_show_position", "BOOLEAN", int(DEFAULT_DYMO_SHOW_POSITION)),
        ("card_w_mm", "REAL", DEFAULT_CARD_W_MM),
        ("card_h_mm", "REAL", DEFAULT_CARD_H_MM),
        ("card_margin_tb_mm", "REAL", DEFAULT_CARD_MARGIN_TB_MM),
        ("card_margin_lr_mm", "REAL", DEFAULT_CARD_MARGIN_LR_MM),
        ("card_gap_mm", "REAL", DEFAULT_CARD_GAP_MM),
        ("card_padding_mm", "REAL", DEFAULT_CARD_PADDING_MM),
        ("card_qr_size_mm", "REAL", DEFAULT_CARD_QR_SIZE_MM),
        ("card_qr_margin_mm", "REAL", DEFAULT_CARD_QR_MARGIN_MM),
        ("card_position_width_mm", "REAL", DEFAULT_CARD_POSITION_WIDTH_MM),
        ("card_position_font_pt", "REAL", DEFAULT_CARD_POSITION_FONT_PT),
        ("card_gap_h_mm", "REAL", DEFAULT_CARD_GAP_H_MM),
        ("card_gap_v_mm", "REAL", DEFAULT_CARD_GAP_V_MM),
        ("card_page_format", "VARCHAR(10)", DEFAULT_CARD_PAGE_FORMAT),
        ("card_orientation_landscape", "BOOLEAN", int(DEFAULT_CARD_ORIENTATION_LANDSCAPE)),
    ]
    added = False
    for col_name, col_type, default_val in new_cols:
        if col_name not in existing_cols:
            try:
                if default_val is None:
                    default_sql = ""
                elif isinstance(default_val, str):
                    default_sql = f" DEFAULT '{default_val}'"
                else:
                    default_sql = f" DEFAULT {default_val}"
                db.session.execute(text(f"ALTER TABLE settings ADD COLUMN {col_name} {col_type}{default_sql}"))
                added = True
            except Exception:
                db.session.rollback()
                return
    if added:
        db.session.commit()

def ensure_item_columns():
    """Garantisce la presenza delle nuove colonne nella tabella items (compatibilità DB esistenti)."""
    try:
        rows = db.session.execute(text("PRAGMA table_info(item)")).fetchall()
    except Exception:
        return
    existing_cols = {r[1] for r in rows}
    added = False
    if "share_drawer" not in existing_cols:
        try:
            db.session.execute(text("ALTER TABLE item ADD COLUMN share_drawer BOOLEAN DEFAULT 0"))
            added = True
        except Exception:
            db.session.rollback()
            return
    if "updated_at" not in existing_cols:
        try:
            db.session.execute(text("ALTER TABLE item ADD COLUMN updated_at DATETIME"))
            db.session.execute(text("UPDATE item SET updated_at = CURRENT_TIMESTAMP WHERE updated_at IS NULL"))
            added = True
        except Exception:
            db.session.rollback()
            return
    if added:
        db.session.commit()

def ensure_category_columns():
    """Aggiunge colonne mancanti nella tabella category (compatibilità DB esistenti)."""
    try:
        rows = db.session.execute(text("PRAGMA table_info(category)")).fetchall()
    except Exception:
        return
    existing_cols = {r[1] for r in rows}
    if "main_measure_mode" not in existing_cols:
        try:
            db.session.execute(text("ALTER TABLE category ADD COLUMN main_measure_mode VARCHAR(16) DEFAULT 'length'"))
            db.session.commit()
        except Exception:
            db.session.rollback()
            return

def ensure_mqtt_settings_columns():
    """Aggiunge eventuali nuove colonne della configurazione MQTT (compatibilità DB esistenti)."""
    try:
        rows = db.session.execute(text("PRAGMA table_info(mqtt_settings)")).fetchall()
    except Exception:
        return
    existing_cols = {r[1] for r in rows}
    new_cols = [
        ("include_item_category_color", "BOOLEAN", 0),
    ]
    added = False
    for col_name, col_type, default_val in new_cols:
        if col_name not in existing_cols:
            try:
                default_sql = f" DEFAULT {default_val}" if default_val is not None else ""
                db.session.execute(text(f"ALTER TABLE mqtt_settings ADD COLUMN {col_name} {col_type}{default_sql}"))
                added = True
            except Exception:
                db.session.rollback()
                return
    if added:
        db.session.commit()

def ensure_katodo_settings_columns():
    """Aggiunge eventuali nuove colonne della configurazione Katodo (compatibilità DB esistenti)."""
    try:
        rows = db.session.execute(text("PRAGMA table_info(katodo_settings)")).fetchall()
    except Exception:
        return
    existing_cols = {r[1] for r in rows}
    new_cols = [
        ("enabled", "BOOLEAN", 0),
        ("api_url",  "VARCHAR(300)", None),
        ("api_key",  "VARCHAR(200)", None),
    ]
    added = False
    for col_name, col_type, default_val in new_cols:
        if col_name not in existing_cols:
            try:
                default_sql = f" DEFAULT {default_val}" if default_val is not None else ""
                db.session.execute(text(f"ALTER TABLE katodo_settings ADD COLUMN {col_name} {col_type}{default_sql}"))
                added = True
            except Exception:
                db.session.rollback()
                return
    if added:
        db.session.commit()

def ensure_slot_columns():
    """Aggiunge eventuali nuove colonne alla tabella slot (compatibilità DB esistenti)."""
    try:
        rows = db.session.execute(text("PRAGMA table_info(slot)")).fetchall()
    except Exception:
        return
    existing_cols = {r[1] for r in rows}
    new_cols = [
        ("display_label_override", "VARCHAR(80)", None),
        ("print_label_override", "VARCHAR(80)", None),
    ]
    added = False
    for col_name, col_type, default_val in new_cols:
        if col_name not in existing_cols:
            try:
                default_sql = f" DEFAULT '{default_val}'" if default_val is not None else ""
                db.session.execute(text(f"ALTER TABLE slot ADD COLUMN {col_name} {col_type}{default_sql}"))
                added = True
            except Exception:
                db.session.rollback()
                return
    if added:
        db.session.commit()

def ensure_user_columns():
    """Aggiunge eventuali nuove colonne alla tabella user (compatibilità DB esistenti)."""
    try:
        rows = db.session.execute(text("PRAGMA table_info(user)")).fetchall()
    except Exception:
        return
    existing_cols = {r[1] for r in rows}
    new_cols = [
        ("role_id", "INTEGER", None),
        ("first_name", "VARCHAR(80)", None),
        ("last_name", "VARCHAR(80)", None),
        ("email", "VARCHAR(120)", None),
        ("avatar_type", "VARCHAR(20)", None),
        ("avatar_value", "VARCHAR(200)", None),
        ("social_links", "TEXT", None),
    ]
    added = False
    for col_name, col_type, default_val in new_cols:
        if col_name not in existing_cols:
            try:
                default_sql = f" DEFAULT '{default_val}'" if default_val is not None else ""
                db.session.execute(text(f"ALTER TABLE user ADD COLUMN {col_name} {col_type}{default_sql}"))
                added = True
            except Exception:
                db.session.rollback()
                return
    if added:
        db.session.commit()

_schema_checked = False
_auth_seeded = False

def ensure_core_schema():
    """Esegue una verifica unica dello schema per aggiungere colonne mancanti."""
    global _schema_checked
    if _schema_checked:
        return
    ensure_settings_columns()
    ensure_item_columns()
    ensure_category_columns()
    ensure_mqtt_settings_columns()
    ensure_katodo_settings_columns()
    ensure_slot_columns()
    ensure_user_columns()
    _schema_checked = True

@app.before_request
def prepare_schema():
    ensure_core_schema()
    global _auth_seeded
    if not _auth_seeded:
        ensure_auth_defaults()
        _auth_seeded = True

@app.before_request
def enforce_login_and_permissions():
    if request.endpoint in {"login", "register", "static"}:
        return None
    try:
        user_count = User.query.count()
    except Exception:
        return None
    if user_count == 0 and request.endpoint not in {"login", "register"}:
        return redirect(url_for("login"))
    if request.path.startswith("/admin"):
        if not current_user.is_authenticated:
            return login_manager.unauthorized()
        required = required_permissions_for_path(request.path)
        if required and not any(current_user.has_permission(p) for p in required):
            flash("Non hai i permessi per accedere a questa sezione.", "danger")
            return redirect(url_for("index"))
    return None

SOCIAL_FIELDS = [
    ("linkedin", "LinkedIn"),
    ("telegram", "Telegram"),
    ("whatsapp", "WhatsApp"),
    ("github", "GitHub"),
    ("x", "X / Twitter"),
]

def _dicebear_url(seed: str) -> str:
    return f"https://api.dicebear.com/7.x/{AVATAR_DICEBEAR_STYLE}/svg?seed={seed}"

def avatar_url_for(user: User | None) -> str | None:
    if not user:
        return None
    if user.avatar_type == "upload" and user.avatar_value:
        return url_for("uploaded_avatar", filename=user.avatar_value)
    if user.avatar_type == "library" and user.avatar_value:
        return _dicebear_url(user.avatar_value)
    if user.username:
        return _dicebear_url(user.username)
    return _dicebear_url(f"user-{user.id}")

def parse_social_links(raw_value: str | None) -> dict:
    if not raw_value:
        return {}
    try:
        data = json.loads(raw_value)
    except json.JSONDecodeError:
        return {}
    if isinstance(data, dict):
        return {str(k): str(v) for k, v in data.items() if v}
    return {}

def build_social_links(form) -> dict:
    data = {}
    for key, _label in SOCIAL_FIELDS:
        value = (form.get(f"social_{key}") or "").strip()
        if value:
            data[key] = value
    return data

def get_settings()->Settings:
    ensure_core_schema()
    s = Settings.query.get(1)
    if not s:
        s = Settings(id=1,
                     label_w_mm=DEFAULT_LABEL_W_MM,
                     label_h_mm=DEFAULT_LABEL_H_MM,
                     margin_tb_mm=DEFAULT_MARG_TB_MM,
                     margin_lr_mm=DEFAULT_MARG_LR_MM,
                     gap_mm=DEFAULT_GAP_MM,
                     label_padding_mm=DEFAULT_LABEL_PADDING_MM,
                     label_qr_size_mm=DEFAULT_LABEL_QR_SIZE_MM,
                     label_qr_margin_mm=DEFAULT_LABEL_QR_MARGIN_MM,
                     label_position_width_mm=DEFAULT_LABEL_POSITION_WIDTH_MM,
                     label_position_font_pt=DEFAULT_LABEL_POSITION_FONT_PT,
                     label_page_format=DEFAULT_LABEL_PAGE_FORMAT,
                     dymo_label_w_mm=DEFAULT_DYMO_LABEL_W_MM,
                     dymo_label_h_mm=DEFAULT_DYMO_LABEL_H_MM,
                     dymo_margin_x_mm=DEFAULT_DYMO_MARGIN_X_MM,
                     dymo_margin_y_mm=DEFAULT_DYMO_MARGIN_Y_MM,
                     dymo_font_name=DEFAULT_DYMO_FONT_NAME,
                     dymo_font_size_pt=DEFAULT_DYMO_FONT_SIZE_PT,
                     dymo_show_category=DEFAULT_DYMO_SHOW_CATEGORY,
                     dymo_show_subtype=DEFAULT_DYMO_SHOW_SUBTYPE,
                     dymo_show_thread=DEFAULT_DYMO_SHOW_THREAD,
                     dymo_show_measure=DEFAULT_DYMO_SHOW_MEASURE,
                     dymo_show_main=DEFAULT_DYMO_SHOW_MAIN,
                     dymo_show_material=DEFAULT_DYMO_SHOW_MATERIAL,
                     dymo_show_position=DEFAULT_DYMO_SHOW_POSITION,
                     card_w_mm=DEFAULT_CARD_W_MM,
                     card_h_mm=DEFAULT_CARD_H_MM,
                     card_margin_tb_mm=DEFAULT_CARD_MARGIN_TB_MM,
                     card_margin_lr_mm=DEFAULT_CARD_MARGIN_LR_MM,
                     card_gap_mm=DEFAULT_CARD_GAP_MM,
                     card_padding_mm=DEFAULT_CARD_PADDING_MM,
                     card_qr_size_mm=DEFAULT_CARD_QR_SIZE_MM,
                     card_qr_margin_mm=DEFAULT_CARD_QR_MARGIN_MM,
                     card_position_width_mm=DEFAULT_CARD_POSITION_WIDTH_MM,
                     card_position_font_pt=DEFAULT_CARD_POSITION_FONT_PT,
                     card_gap_h_mm=DEFAULT_CARD_GAP_H_MM,
                     card_gap_v_mm=DEFAULT_CARD_GAP_V_MM,
                     card_page_format=DEFAULT_CARD_PAGE_FORMAT,
                     orientation_landscape=DEFAULT_ORIENTATION_LANDSCAPE,
                     card_orientation_landscape=DEFAULT_CARD_ORIENTATION_LANDSCAPE,
                     qr_default=DEFAULT_QR_DEFAULT,
                     qr_base_url=DEFAULT_QR_BASE_URL)
        db.session.add(s); db.session.commit()
    changed = False
    if s.label_padding_mm is None: s.label_padding_mm = DEFAULT_LABEL_PADDING_MM; changed = True
    if s.label_qr_size_mm is None: s.label_qr_size_mm = DEFAULT_LABEL_QR_SIZE_MM; changed = True
    if s.label_qr_margin_mm is None: s.label_qr_margin_mm = DEFAULT_LABEL_QR_MARGIN_MM; changed = True
    if s.label_position_width_mm is None: s.label_position_width_mm = DEFAULT_LABEL_POSITION_WIDTH_MM; changed = True
    if s.label_position_font_pt is None: s.label_position_font_pt = DEFAULT_LABEL_POSITION_FONT_PT; changed = True
    normalized_label_format = normalize_page_format(getattr(s, "label_page_format", None), DEFAULT_LABEL_PAGE_FORMAT)
    if getattr(s, "label_page_format", None) != normalized_label_format:
        s.label_page_format = normalized_label_format
        changed = True
    if getattr(s, "dymo_label_w_mm", None) is None: s.dymo_label_w_mm = DEFAULT_DYMO_LABEL_W_MM; changed = True
    if getattr(s, "dymo_label_h_mm", None) is None: s.dymo_label_h_mm = DEFAULT_DYMO_LABEL_H_MM; changed = True
    if getattr(s, "dymo_margin_x_mm", None) is None: s.dymo_margin_x_mm = DEFAULT_DYMO_MARGIN_X_MM; changed = True
    if getattr(s, "dymo_margin_y_mm", None) is None: s.dymo_margin_y_mm = DEFAULT_DYMO_MARGIN_Y_MM; changed = True
    if getattr(s, "dymo_font_name", None) in (None, ""): s.dymo_font_name = DEFAULT_DYMO_FONT_NAME; changed = True
    if getattr(s, "dymo_font_size_pt", None) is None: s.dymo_font_size_pt = DEFAULT_DYMO_FONT_SIZE_PT; changed = True
    if getattr(s, "dymo_show_category", None) is None: s.dymo_show_category = DEFAULT_DYMO_SHOW_CATEGORY; changed = True
    if getattr(s, "dymo_show_subtype", None) is None: s.dymo_show_subtype = DEFAULT_DYMO_SHOW_SUBTYPE; changed = True
    if getattr(s, "dymo_show_thread", None) is None: s.dymo_show_thread = DEFAULT_DYMO_SHOW_THREAD; changed = True
    if getattr(s, "dymo_show_measure", None) is None: s.dymo_show_measure = DEFAULT_DYMO_SHOW_MEASURE; changed = True
    if getattr(s, "dymo_show_main", None) is None: s.dymo_show_main = DEFAULT_DYMO_SHOW_MAIN; changed = True
    if getattr(s, "dymo_show_material", None) is None: s.dymo_show_material = DEFAULT_DYMO_SHOW_MATERIAL; changed = True
    if getattr(s, "dymo_show_position", None) is None: s.dymo_show_position = DEFAULT_DYMO_SHOW_POSITION; changed = True
    if s.card_w_mm is None: s.card_w_mm = DEFAULT_CARD_W_MM; changed = True
    if s.card_h_mm is None: s.card_h_mm = DEFAULT_CARD_H_MM; changed = True
    if getattr(s, "card_margin_tb_mm", None) is None: s.card_margin_tb_mm = DEFAULT_CARD_MARGIN_TB_MM; changed = True
    if getattr(s, "card_margin_lr_mm", None) is None: s.card_margin_lr_mm = DEFAULT_CARD_MARGIN_LR_MM; changed = True
    if getattr(s, "card_gap_mm", None) is None:
        legacy_gap = getattr(s, "card_gap_h_mm", None) or getattr(s, "card_gap_v_mm", None)
        s.card_gap_mm = legacy_gap if legacy_gap is not None else DEFAULT_CARD_GAP_MM
        changed = True
    if getattr(s, "card_padding_mm", None) is None: s.card_padding_mm = DEFAULT_CARD_PADDING_MM; changed = True
    if getattr(s, "card_qr_size_mm", None) is None: s.card_qr_size_mm = DEFAULT_CARD_QR_SIZE_MM; changed = True
    if getattr(s, "card_qr_margin_mm", None) is None: s.card_qr_margin_mm = DEFAULT_CARD_QR_MARGIN_MM; changed = True
    if getattr(s, "card_position_width_mm", None) is None: s.card_position_width_mm = DEFAULT_CARD_POSITION_WIDTH_MM; changed = True
    if getattr(s, "card_position_font_pt", None) is None: s.card_position_font_pt = DEFAULT_CARD_POSITION_FONT_PT; changed = True
    if getattr(s, "card_gap_h_mm", None) is None: s.card_gap_h_mm = DEFAULT_CARD_GAP_H_MM; changed = True
    if getattr(s, "card_gap_v_mm", None) is None: s.card_gap_v_mm = DEFAULT_CARD_GAP_V_MM; changed = True
    normalized_card_format = normalize_page_format(getattr(s, "card_page_format", None), DEFAULT_CARD_PAGE_FORMAT)
    if getattr(s, "card_page_format", None) != normalized_card_format:
        s.card_page_format = normalized_card_format
        changed = True
    if getattr(s, "card_orientation_landscape", None) is None:
        s.card_orientation_landscape = DEFAULT_CARD_ORIENTATION_LANDSCAPE
        changed = True
    if changed:
        db.session.commit()
    return s

def get_mqtt_settings() -> MqttSettings:
    ensure_core_schema()
    s = MqttSettings.query.get(1)
    if not s:
        s = MqttSettings(
            id=1,
            enabled=False,
            host=DEFAULT_MQTT_HOST,
            port=DEFAULT_MQTT_PORT,
            topic=DEFAULT_MQTT_TOPIC,
            qos=DEFAULT_MQTT_QOS,
            retain=DEFAULT_MQTT_RETAIN,
        )
        db.session.add(s)
        db.session.commit()
    return s

def get_katodo_settings() -> KatodoSettings:
    ensure_core_schema()
    s = KatodoSettings.query.get(1)
    if not s:
        s = KatodoSettings(
            id=1,
            enabled=False,
            api_url="https://katodo.com/api/",
            api_key=None,
        )
        db.session.add(s)
        db.session.commit()
    return s

def prestashop_api_request(path: str, settings: KatodoSettings, params: dict = None, timeout: int = 10) -> dict:
    """Esegue GET al WebService PrestaShop. Restituisce {ok, data, status_code, error}."""
    import requests as _requests
    if not settings.enabled:
        return {"ok": False, "data": None, "status_code": None, "error": "Integrazione Katodo non abilitata."}
    if not settings.api_key or not settings.api_url:
        return {"ok": False, "data": None, "status_code": None, "error": "API key o URL non configurati."}
    base = settings.api_url.rstrip("/")
    url = f"{base}/{path.lstrip('/')}" if path else f"{base}/"
    merged_params = {"output_format": "JSON"}
    if params:
        merged_params.update(params)
    merged_params["ws_key"] = settings.api_key  # nginx strips Authorization header on shared hosting
    try:
        resp = _requests.get(url, params=merged_params, timeout=timeout)
        if resp.status_code == 200:
            try:
                data = resp.json()
            except ValueError:
                data = {"raw": resp.text}
            return {"ok": True, "data": data, "status_code": 200, "error": None}
        return {"ok": False, "data": None, "status_code": resp.status_code, "error": f"HTTP {resp.status_code}: {resp.text[:300]}"}
    except Exception as exc:
        return {"ok": False, "data": None, "status_code": None, "error": str(exc)}

def ps_image_url(api_url: str, image_id: int, size: str = "home_default") -> str:
    """Costruisce l'URL diretto dell'immagine PrestaShop senza richiedere autenticazione."""
    from urllib.parse import urlparse
    parsed = urlparse(api_url or "https://katodo.com/api/")
    base = f"{parsed.scheme}://{parsed.netloc}"
    digits = "/".join(str(image_id))
    return f"{base}/img/p/{digits}/{image_id}-{size}.jpg"

def get_or_create_permission(key: str, label: str, description: Optional[str] = None, is_system: bool = False) -> Permission:
    perm = Permission.query.filter_by(key=key).first()
    if not perm:
        perm = Permission(key=key, label=label, description=description, is_system=is_system)
        db.session.add(perm)
        db.session.flush()
    return perm

def get_or_create_role(name: str, description: Optional[str] = None, is_system: bool = False) -> Role:
    role = Role.query.filter_by(name=name).first()
    if not role:
        role = Role(name=name, description=description, is_system=is_system)
        db.session.add(role)
        db.session.flush()
    return role

def ensure_auth_defaults():
    default_permissions = [
        ("manage_items", "Gestione articoli", "Creazione e modifica articoli", True),
        ("manage_placements", "Posizionamento articoli", "Assegnazione e spostamenti", True),
        ("manage_config", "Configurazione catalogo", "Categorie, materiali, campi e impostazioni", True),
        ("manage_locations", "Gestione ubicazioni", "Cassettiere, ubicazioni e slot", True),
        ("manage_users", "Gestione utenti", "Assegnazione ruoli agli utenti", True),
        ("manage_roles", "Configurazione ruoli", "Creazione ruoli e permessi", True),
        ("manage_katodo", "Katodo.com", "Accesso ai dati del negozio PrestaShop katodo.com", True),
    ]
    perms_by_key = {}
    for key, label, description, is_system in default_permissions:
        perms_by_key[key] = get_or_create_permission(key, label, description, is_system=is_system)

    admin_role = get_or_create_role("Admin", "Accesso completo", is_system=True)
    operator_role = get_or_create_role("Operatore", "Gestione articoli e posizionamento", is_system=True)
    viewer_role = get_or_create_role("Lettore", "Accesso in sola lettura", is_system=True)

    if not admin_role.permissions:
        admin_role.permissions = list(perms_by_key.values())
    else:
        existing_keys = {p.key for p in admin_role.permissions}
        for perm in perms_by_key.values():
            if perm.key not in existing_keys:
                admin_role.permissions.append(perm)
    if not operator_role.permissions:
        operator_role.permissions = [
            perms_by_key["manage_items"],
            perms_by_key["manage_placements"],
        ]

    db.session.flush()

    if User.query.count() == 0:
        admin_user = User(username="admin", role=admin_role)
        admin_user.set_password("admin")
        db.session.add(admin_user)
        db.session.flush()

    users_without_role = User.query.filter(User.role_id.is_(None)).order_by(User.id).all()
    if users_without_role:
        first_user_id = users_without_role[0].id
        for user in users_without_role:
            if user.username == "admin" or user.id == first_user_id:
                user.role = admin_role
            else:
                user.role = viewer_role

    db.session.commit()

def required_permissions_for_path(path: str) -> Optional[set]:
    if path.startswith("/admin/config"):
        return {"manage_config", "manage_users", "manage_roles"}
    if path.startswith("/admin/users"):
        return {"manage_users"}
    if path.startswith("/admin/roles") or path.startswith("/admin/permissions"):
        return {"manage_roles"}
    if path.startswith("/admin/categories") or path.startswith("/admin/subtypes"):
        return {"manage_config"}
    if path.startswith("/admin/materials") or path.startswith("/admin/finishes"):
        return {"manage_config"}
    if path.startswith("/admin/custom_fields") or path.startswith("/admin/settings") or path.startswith("/admin/mqtt"):
        return {"manage_config"}
    if path.startswith("/admin/locations") or path.startswith("/admin/cabinets") or path.startswith("/admin/slots"):
        return {"manage_locations"}
    if path.startswith("/admin/posizionamento") or path.startswith("/admin/to_place"):
        return {"manage_placements"}
    if path.startswith("/admin/unplaced") or path.startswith("/admin/grid_assign"):
        return {"manage_placements"}
    if path.startswith("/admin/auto_assign") or path.startswith("/admin/slot_items") or path.startswith("/admin/slot_label"):
        return {"manage_placements"}
    if path.startswith("/admin/items"):
        if any(keyword in path for keyword in ["set_position", "clear_position", "move_slot", "suggest_position"]):
            return {"manage_placements"}
        return {"manage_items"}
    if path.startswith("/admin/labels") or path.startswith("/admin/cards") or path.startswith("/admin/dymo") or path.startswith("/admin/items/export") or path.startswith("/admin/data"):
        return {"manage_items"}
    if path == "/admin":
        return {"manage_items"}
    if path.startswith("/admin/katodo"):
        return {"manage_katodo"}
    return None

def mqtt_payload_for_slot(cabinet: Cabinet, col_code: str, row_num: int, settings: MqttSettings):
    if not cabinet:
        return None
    region = merge_region_for(cabinet.id, col_code, row_num)
    if region:
        col_code = region["anchor_col"]
        row_num = region["anchor_row"]
    location = Location.query.get(cabinet.location_id) if cabinet else None
    slot_obj = Slot.query.filter_by(cabinet_id=cabinet.id, col_code=col_code, row_num=row_num).first()
    slot_label_text = slot_label(slot_obj, for_display=True, fallback_col=col_code, fallback_row=row_num)
    payload = {
        "event": "slot_click",
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }
    if settings.include_cabinet_name:
        payload["cabinet_name"] = cabinet.name if cabinet else None
    if settings.include_cabinet_id:
        payload["cabinet_id"] = cabinet.id if cabinet else None
    if settings.include_location_name:
        payload["location_name"] = location.name if location else None
    if settings.include_location_id:
        payload["location_id"] = location.id if location else None
    if settings.include_row:
        payload["row"] = row_num
    if settings.include_col:
        payload["col"] = col_code
    if settings.include_slot_label:
        payload["slot"] = slot_label_text

    if settings.include_items:
        region = merge_region_for(cabinet.id, col_code, row_num)
        if region:
            cells = merge_cells_from_region(region)
        else:
            cells = [(col_code, row_num)]
        slots = (
            Slot.query.filter(Slot.cabinet_id == cabinet.id)
            .filter(or_(*[
                (Slot.col_code == col) & (Slot.row_num == row)
                for col, row in cells
            ]))
            .all()
        )
        items_payload = []
        if slots:
            slot_ids = [s.id for s in slots]
            assigns = (
                db.session.query(Assignment, Item, Category, Slot)
                .join(Item, Assignment.item_id == Item.id)
                .join(Category, Item.category_id == Category.id, isouter=True)
                .join(Slot, Assignment.slot_id == Slot.id)
                .filter(Assignment.slot_id.in_(slot_ids))
                .order_by(Slot.col_code, Slot.row_num, Assignment.compartment_no)
                .all()
            )
            for a, it, cat, slot in assigns:
                item_data = {}
                if settings.include_item_id:
                    item_data["id"] = it.id
                if settings.include_item_name:
                    item_data["name"] = auto_name_for(it)
                if settings.include_item_category:
                    item_data["category"] = cat.name if cat else None
                if settings.include_item_category_color:
                    item_data["category_color"] = cat.color if cat else None
                if settings.include_item_quantity:
                    item_data["quantity"] = it.quantity
                if settings.include_item_position:
                    item_data["position"] = slot_label(slot, for_display=True, fallback_col=slot.col_code, fallback_row=slot.row_num)
                if settings.include_item_description:
                    item_data["description"] = it.description
                if settings.include_item_material:
                    item_data["material"] = it.material.name if it.material else None
                if settings.include_item_finish:
                    item_data["finish"] = it.finish.name if it.finish else None
                items_payload.append(item_data)
        if items_payload or settings.include_empty:
            payload["items"] = items_payload
        else:
            return None
    return payload

def publish_mqtt_payload(payload: dict, settings: MqttSettings):
    if not settings.enabled:
        return {"ok": False, "skipped": True, "error": "MQTT disabilitato."}
    if not settings.host or not settings.topic:
        return {"ok": False, "error": "Configurazione MQTT incompleta."}
    from paho.mqtt import publish as mqtt_publish
    auth = None
    if settings.username:
        auth = {"username": settings.username, "password": settings.password or ""}
    try:
        mqtt_publish.single(
            settings.topic,
            json.dumps(payload, ensure_ascii=False),
            hostname=settings.host,
            port=settings.port or DEFAULT_MQTT_PORT,
            qos=settings.qos or DEFAULT_MQTT_QOS,
            retain=bool(settings.retain),
            client_id=settings.client_id or None,
            auth=auth,
        )
        return {"ok": True}
    except Exception as exc:
        return {"ok": False, "error": str(exc)}

@app.context_processor
def inject_utils():
    return dict(
        compose_caption=auto_name_for,
        app_settings=get_settings,
        measure_label_for_category=measure_label_for_category,
        formatted_main_measure=formatted_main_measure,
        main_measure_value=main_measure_value,
    )

def load_form_options():
    thread_standards = ThreadStandard.query.order_by(ThreadStandard.sort_order, ThreadStandard.label).all()
    thread_sizes = (
        ThreadSize.query.join(ThreadStandard)
        .order_by(ThreadStandard.sort_order, ThreadSize.sort_order, ThreadSize.value)
        .all()
    )
    sizes_by_standard = {}
    for size in thread_sizes:
        sizes_by_standard.setdefault(size.standard.code, []).append(size.value)
    return thread_standards, sizes_by_standard

BUILTIN_FIELD_DEFS = [
    {"key": "subtype_id", "label": "Sottotipo (forma)"},
    {"key": "thread_standard", "label": "Standard"},
    {"key": "thread_size", "label": "Misura"},
    {"key": "outer_d_mm", "label": "Ø esterno (mm)"},
    {"key": "length_mm", "label": "Lunghezza/Spessore (mm)"},
    {"key": "inner_d_mm", "label": "Ø interno (mm)"},
    {"key": "material_id", "label": "Materiale"},
    {"key": "finish_id", "label": "Finitura"},
    {"key": "description", "label": "Descrizione"},
    {"key": "quantity", "label": "Quantità"},
]

def custom_field_key(field_id: int) -> str:
    return f"custom_{field_id}"

def parse_custom_field_options(raw: str) -> list:
    if not raw:
        return []
    lines = raw.replace(",", "\n").splitlines()
    return [opt.strip() for opt in lines if opt.strip()]

def default_fields_for_category(cat_name: str) -> set:
    base = {
        "subtype_id",
        "thread_standard",
        "thread_size",
        "material_id",
        "finish_id",
        "description",
        "quantity",
    }
    if not cat_name:
        base.update({"outer_d_mm", "length_mm"})
        return base
    lower = cat_name.strip().lower()
    if lower in {"viti", "torrette", "distanziali"}:
        base.add("length_mm")
    else:
        base.add("outer_d_mm")
    if lower == "rondelle":
        base.update({"inner_d_mm", "length_mm"})
    return base

def serialize_custom_fields(fields):
    return [
        {
            "id": f.id,
            "name": f.name,
            "field_type": f.field_type,
            "options": parse_custom_field_options(f.options),
            "unit": f.unit,
            "sort_order": f.sort_order,
            "is_active": f.is_active,
        }
        for f in fields
    ]

def build_category_field_map(categories):
    settings = CategoryFieldSetting.query.all()
    enabled_by_cat = {}
    configured_cats = set()
    for setting in settings:
        configured_cats.add(setting.category_id)
        if setting.is_enabled and setting.field_key != "__none__":
            enabled_by_cat.setdefault(setting.category_id, set()).add(setting.field_key)
    for cat_id, enabled_fields in enabled_by_cat.items():
        if "thickness_mm" in enabled_fields:
            enabled_fields.add("length_mm")
    for cat in categories:
        if cat.id not in configured_cats:
            enabled_by_cat[cat.id] = default_fields_for_category(cat.name)
        elif cat.id not in enabled_by_cat:
            enabled_by_cat[cat.id] = set()
    return {cat_id: sorted(keys) for cat_id, keys in enabled_by_cat.items()}

def get_used_field_keys_by_category():
    used = {}
    rows = db.session.query(
        Item.category_id,
        Item.subtype_id,
        Item.thread_standard,
        Item.thread_size,
        Item.outer_d_mm,
        Item.length_mm,
        Item.inner_d_mm,
        Item.material_id,
        Item.finish_id,
        Item.description,
        Item.quantity,
        Item.thickness_mm,
    ).all()

    for (
        category_id,
        subtype_id,
        thread_standard,
        thread_size,
        outer_d_mm,
        length_mm,
        inner_d_mm,
        material_id,
        finish_id,
        description,
        quantity,
        thickness_mm,
    ) in rows:
        cat_used = used.setdefault(category_id, set())
        if subtype_id is not None:
            cat_used.add("subtype_id")
        if thread_standard:
            cat_used.add("thread_standard")
        if thread_size:
            cat_used.add("thread_size")
        if outer_d_mm is not None:
            cat_used.add("outer_d_mm")
        if length_mm is not None:
            cat_used.add("length_mm")
        if thickness_mm is not None:
            cat_used.update({"thickness_mm", "length_mm"})
        if inner_d_mm is not None:
            cat_used.add("inner_d_mm")
        if material_id is not None:
            cat_used.add("material_id")
        if finish_id is not None:
            cat_used.add("finish_id")
        if description:
            cat_used.add("description")
        if quantity is not None:
            cat_used.add("quantity")

    custom_values = (
        db.session.query(Item.category_id, ItemCustomFieldValue.field_id)
        .join(Item, Item.id == ItemCustomFieldValue.item_id)
        .distinct()
        .all()
    )
    for category_id, field_id in custom_values:
        used.setdefault(category_id, set()).add(custom_field_key(field_id))

    return {cat_id: sorted(keys) for cat_id, keys in used.items()}

def build_field_definitions(custom_fields):
    defs = [{"key": f["key"], "label": f["label"], "is_custom": False} for f in BUILTIN_FIELD_DEFS]
    for field in custom_fields:
        label = field["name"]
        if field.get("unit"):
            label = f"{label} ({field['unit']})"
        defs.append({
            "key": custom_field_key(field["id"]),
            "label": f"Personalizzato: {label}",
            "is_custom": True,
        })
    return defs

def parse_length_thickness_value(raw_value):
    if raw_value is None or raw_value == "":
        return None
    return float(raw_value)


def split_main_measure_for_category(category: Category | None, raw_value):
    """Restituisce la misura principale separata in lunghezza o spessore in base alla categoria."""
    value = parse_length_thickness_value(raw_value)
    if value is None:
        return None, None
    mode = measure_mode_for_category(category)
    if mode == "thickness":
        return None, value
    return value, None

def save_custom_field_values(item: Item, form):
    active_fields = CustomField.query.filter_by(is_active=True).all()
    existing = {
        val.field_id: val
        for val in ItemCustomFieldValue.query.filter_by(item_id=item.id).all()
    }
    for field in active_fields:
        form_key = f"custom_field_{field.id}"
        if form_key not in form:
            continue
        raw = (form.get(form_key) or "").strip()
        if not raw:
            if field.id in existing:
                db.session.delete(existing[field.id])
            continue
        if field.id in existing:
            existing[field.id].value_text = raw
        else:
            db.session.add(ItemCustomFieldValue(item_id=item.id, field_id=field.id, value_text=raw))

# ===================== AUTH =====================
@login_manager.user_loader
def load_user(user_id):
    return db.session.get(User, int(user_id))

@app.route("/login", methods=["GET","POST"])
def login():
    if request.method == "POST":
        username = (request.form.get("username") or "").strip()
        password = request.form.get("password") or ""
        user = User.query.filter_by(username=username).first()
        if user and user.check_password(password):
            if not (user.password.startswith("pbkdf2:") or user.password.startswith("scrypt:")):
                user.set_password(password)
                db.session.commit()
            login_user(user, remember=True)
            if user.has_permission("manage_items"):
                return redirect(url_for("admin_items"))
            return redirect(url_for("index"))
        flash("Credenziali non valide", "danger")
    return render_template("login.html")

@app.route("/register", methods=["POST"])
def register():
    username = (request.form.get("username") or "").strip()
    password = request.form.get("password") or ""
    confirm = request.form.get("confirm_password") or ""
    if len(username) < 3:
        return _flash_back("Username troppo corto (minimo 3 caratteri).", "danger", "login")
    if len(password) < 6:
        return _flash_back("Password troppo corta (minimo 6 caratteri).", "danger", "login")
    if password != confirm:
        return _flash_back("Le password non coincidono.", "danger", "login")
    if User.query.filter_by(username=username).first():
        return _flash_back("Username già utilizzato.", "danger", "login")

    role = Role.query.filter_by(name="Lettore").first()
    if User.query.count() == 0:
        role = Role.query.filter_by(name="Admin").first()
    if role is None:
        role = get_or_create_role("Lettore", "Accesso in sola lettura", is_system=True)

    user = User(username=username, role=role)
    user.set_password(password)
    db.session.add(user)
    db.session.commit()
    login_user(user, remember=True)
    flash("Registrazione completata.", "success")
    if user.has_permission("manage_items"):
        return redirect(url_for("admin_items"))
    return redirect(url_for("index"))

@app.route("/logout")
@login_required
def logout():
    logout_user()
    session.clear()
    response = redirect(url_for("index"))
    response.delete_cookie(app.config.get("REMEMBER_COOKIE_NAME", "remember_token"))
    return response

@app.route("/uploads/avatars/<path:filename>")
@login_required
def uploaded_avatar(filename):
    return send_from_directory(AVATAR_UPLOAD_DIR, filename)

@app.route("/profilo", methods=["GET", "POST"])
@login_required
def profile():
    if request.method == "POST":
        action = request.form.get("action")
        if action == "profile":
            current_user.first_name = (request.form.get("first_name") or "").strip()
            current_user.last_name = (request.form.get("last_name") or "").strip()
            current_user.email = (request.form.get("email") or "").strip()
            social_links = build_social_links(request.form)
            current_user.social_links = json.dumps(social_links, ensure_ascii=False)
            db.session.commit()
            flash("Profilo aggiornato.", "success")
        elif action == "password":
            old_password = request.form.get("old_password") or ""
            new_password = request.form.get("new_password") or ""
            confirm_password = request.form.get("confirm_password") or ""
            if not current_user.check_password(old_password):
                flash("La password attuale non è corretta.", "danger")
            elif len(new_password) < 6:
                flash("La nuova password è troppo corta (minimo 6 caratteri).", "danger")
            elif new_password != confirm_password:
                flash("Le nuove password non coincidono.", "danger")
            else:
                current_user.set_password(new_password)
                db.session.commit()
                flash("Password aggiornata.", "success")
        elif action == "avatar_library":
            seed = (request.form.get("avatar_seed") or "").strip()
            if not seed:
                flash("Seleziona un avatar dalla libreria.", "danger")
            else:
                current_user.avatar_type = "library"
                current_user.avatar_value = seed
                db.session.commit()
                flash("Avatar aggiornato.", "success")
        elif action == "avatar_upload":
            file = request.files.get("avatar_file")
            if not file or not file.filename:
                flash("Seleziona un file immagine.", "danger")
            else:
                ext = file.filename.rsplit(".", 1)[-1].lower()
                if ext not in AVATAR_ALLOWED_EXTS:
                    flash("Formato non supportato. Usa PNG, JPG o WEBP.", "danger")
                else:
                    os.makedirs(AVATAR_UPLOAD_DIR, exist_ok=True)
                    filename = secure_filename(file.filename)
                    unique_name = f"{uuid.uuid4().hex}_{filename}"
                    path = os.path.join(AVATAR_UPLOAD_DIR, unique_name)
                    file.save(path)
                    if current_user.avatar_type == "upload" and current_user.avatar_value:
                        old_path = os.path.join(AVATAR_UPLOAD_DIR, current_user.avatar_value)
                        if os.path.exists(old_path):
                            os.remove(old_path)
                    current_user.avatar_type = "upload"
                    current_user.avatar_value = unique_name
                    db.session.commit()
                    flash("Avatar personalizzato caricato.", "success")
        return redirect(url_for("profile"))
    social_values = parse_social_links(current_user.social_links)
    return render_template(
        "profile.html",
        social_values=social_values,
        social_fields=SOCIAL_FIELDS,
        avatar_library_seeds=AVATAR_LIBRARY_SEEDS,
        dicebear_style=AVATAR_DICEBEAR_STYLE,
    )

@app.context_processor
def inject_user_avatar():
    return {"current_user_avatar": avatar_url_for(current_user) if current_user.is_authenticated else None}

# ===================== PUBLIC =====================
def _render_articles_page():
    ensure_core_schema()
    low_stock_threshold = 5
    items_q    = Item.query.options(
        selectinload(Item.category),
        selectinload(Item.material),
        selectinload(Item.finish),
        selectinload(Item.subtype),
    )
    text_q = (request.args.get("q") or "").strip()
    category_id = request.args.get("category_id", type=int)
    subtype_id = request.args.get("subtype_id", type=int)
    material_id = request.args.get("material_id", type=int)
    finish_id = request.args.get("finish_id", type=int)
    measure_q = (request.args.get("measure") or request.args.get("thread_size") or "").strip()
    share_filter = request.args.get("share_drawer")
    stock_filter = request.args.get("stock")
    pos_cabinet_id = request.args.get("pos_cabinet_id", type=int)
    pos_col = (request.args.get("pos_col") or "").strip().upper()
    pos_row = request.args.get("pos_row", type=int)
    modified_recent_days = request.args.get("modified_recent_days", type=int)
    modified_from = (request.args.get("modified_from") or "").strip()
    modified_to = (request.args.get("modified_to") or "").strip()

    if text_q:
        text_q_lower = text_q.lower()
        items_q = items_q.filter(or_(
            func.lower(Item.name).contains(text_q_lower),
            func.lower(Item.description).contains(text_q_lower),
            func.lower(Item.thread_size).contains(text_q_lower),
            func.strftime('%Y-%m-%d %H:%M', Item.updated_at).contains(text_q_lower),
        ))
    if category_id:
        items_q = items_q.filter(Item.category_id == category_id)
    if subtype_id:
        items_q = items_q.filter(Item.subtype_id == subtype_id)
    if material_id:
        items_q = items_q.filter(Item.material_id == material_id)
    if finish_id:
        items_q = items_q.filter(Item.finish_id == finish_id)
    if measure_q:
        items_q = items_q.filter(func.lower(Item.thread_size).contains(measure_q.lower()))
    if share_filter == "1":
        items_q = items_q.filter(Item.share_drawer.is_(True))
    elif share_filter == "0":
        items_q = items_q.filter(Item.share_drawer.is_(False))
    if stock_filter == "available":
        items_q = items_q.filter(Item.quantity > 0)
    elif stock_filter == "low":
        items_q = items_q.filter(Item.quantity <= low_stock_threshold)
    elif stock_filter == "out":
        items_q = items_q.filter(Item.quantity <= 0)

    if pos_cabinet_id or pos_col or pos_row:
        pos_q = db.session.query(Assignment.item_id).join(Slot, Assignment.slot_id == Slot.id)
        if pos_cabinet_id:
            pos_q = pos_q.filter(Slot.cabinet_id == pos_cabinet_id)
        if pos_col:
            pos_q = pos_q.filter(Slot.col_code == pos_col)
        if pos_row:
            pos_q = pos_q.filter(Slot.row_num == pos_row)
        items_q = items_q.filter(Item.id.in_(pos_q))

    if modified_recent_days:
        threshold = datetime.utcnow() - timedelta(days=max(1, modified_recent_days))
        items_q = items_q.filter(Item.updated_at >= threshold)
    if modified_from:
        try:
            from_dt = datetime.strptime(modified_from, "%Y-%m-%d")
            items_q = items_q.filter(Item.updated_at >= from_dt)
        except ValueError:
            pass
    if modified_to:
        try:
            to_dt = datetime.strptime(modified_to, "%Y-%m-%d") + timedelta(days=1)
            items_q = items_q.filter(Item.updated_at < to_dt)
        except ValueError:
            pass
    items = items_q.all()

    categories = Category.query.order_by(Category.name).all()
    subtypes   = Subtype.query.order_by(Subtype.name).all()
    materials  = Material.query.order_by(Material.name).all()
    finishes   = Finish.query.order_by(Finish.name).all()
    locations  = Location.query.order_by(Location.name).all()
    cabinets   = Cabinet.query.order_by(Cabinet.name).all()
    measure_labels = build_measure_labels(categories)

    assignments = (
        db.session.query(Assignment.item_id, Cabinet, Slot)
        .join(Slot, Assignment.slot_id == Slot.id)
        .join(Cabinet, Slot.cabinet_id == Cabinet.id)
        .all()
    )
    pos_by_item = {
        item_id: slot_full_label(cab, slot, for_print=False)
        for item_id, cab, slot in assignments
    }

    thread_standards, sizes_by_standard = load_form_options()
    default_standard_code = next(
        (s.code for s in thread_standards if s.code == "M"),
        thread_standards[0].code if thread_standards else "",
    )

    subtypes_by_cat = {}
    for s in subtypes:
        subtypes_by_cat.setdefault(s.category_id, []).append({"id": s.id, "name": s.name})

    custom_fields = CustomField.query.filter_by(is_active=True).order_by(CustomField.sort_order, CustomField.name).all()
    serialized_custom_fields = serialize_custom_fields(custom_fields)
    category_fields = build_category_field_map(categories)

    subq = select(Assignment.item_id)
    unplaced_count = Item.query.filter(Item.id.not_in(subq)).count()
    low_stock_count = Item.query.filter(Item.quantity <= low_stock_threshold).count()
    total_items = Item.query.count()
    total_categories = Category.query.count()

    can_manage_items = current_user.is_authenticated and current_user.has_permission("manage_items")
    can_manage_placements = current_user.is_authenticated and current_user.has_permission("manage_placements")
    current_url = request.full_path
    if current_url.endswith("?"):
        current_url = current_url[:-1]
    return render_template("articles.html",
        items=items, categories=categories, materials=materials, finishes=finishes,
        locations=locations, cabinets=cabinets,
        subtypes_by_cat=subtypes_by_cat,
        thread_standards=thread_standards,
        sizes_by_standard=sizes_by_standard,
        default_standard_code=default_standard_code,
        pos_by_item=pos_by_item,
        custom_fields=serialized_custom_fields,
        subtypes=subtypes,
        category_fields=category_fields,
        unplaced_count=unplaced_count,
        low_stock_count=low_stock_count,
        total_items=total_items,
        total_categories=total_categories,
        low_stock_threshold=low_stock_threshold,
        can_manage_items=can_manage_items,
        can_manage_placements=can_manage_placements,
        stock_filter=stock_filter,
        measure_q=measure_q,
        modified_recent_days=modified_recent_days,
        modified_from=modified_from,
        modified_to=modified_to,
        measure_labels=measure_labels,
        current_url=current_url,
    )

@app.route("/")
def index():
    return _render_articles_page()

@app.route("/articoli")
def articles():
    return _render_articles_page()

def build_full_grid(cabinet_id:int):
    cab = db.session.get(Cabinet, cabinet_id)
    if not cab: return {"rows":[], "cols":[], "cells":{}, "cab":None}

    rows = list(range(1, min(128, max(1, int(cab.rows_max))) + 1))
    cols = list(iter_cols_upto(cab.cols_max or "Z"))
    merge_anchors = {}
    merge_skips = {}
    merge_regions = {}

    merges = DrawerMerge.query.filter_by(cabinet_id=cabinet_id).all()
    for m in merges:
        try:
            row_start, row_end, col_start, col_end = normalize_merge_bounds(
                cab, m.col_start, m.col_end, m.row_start, m.row_end
            )
        except ValueError:
            continue
        start_idx = colcode_to_idx(col_start)
        end_idx = colcode_to_idx(col_end)
        anchor_key = f"{col_start}-{row_start}"
        merge_anchors[anchor_key] = {"rowspan": row_end - row_start + 1, "colspan": end_idx - start_idx + 1}
        merge_regions[anchor_key] = {
            "row_start": row_start,
            "row_end": row_end,
            "col_start": col_start,
            "col_end": col_end,
        }
        for row in range(row_start, row_end + 1):
            for col_idx in range(start_idx, end_idx + 1):
                key = f"{idx_to_colcode(col_idx)}-{row}"
                if key != anchor_key:
                    merge_skips[key] = True

    slot_rows = (
        db.session.query(Slot)
        .filter(Slot.cabinet_id == cabinet_id)
        .all()
    )
    slot_display_labels = {}
    slot_display_custom = {}
    slot_id_by_key = {}
    for s in slot_rows:
        key = f"{s.col_code}-{s.row_num}"
        slot_display_labels[key] = slot_label(s, for_display=True)
        slot_display_custom[key] = bool((s.display_label_override or "").strip())
        slot_id_by_key[key] = s.id

    assigns = (
        db.session.query(Assignment, Slot, Item, Category)
        .join(Slot, Assignment.slot_id == Slot.id)
        .join(Item, Assignment.item_id == Item.id)
        .join(Category, Item.category_id == Category.id, isouter=True)
        .filter(Slot.cabinet_id == cabinet_id)
        .all()
    )

    cells = {}
    for s in slot_rows:
        key = f"{s.col_code}-{s.row_num}"
        cells[key] = {
            "blocked": bool(s.is_blocked),
            "entries": [],
            "cat_id": None,
            "label": slot_display_labels.get(key) or f"{s.col_code}{s.row_num}",
            "label_custom": slot_display_custom.get(key, False),
            "items": [],
            "auto_label": False,
            "slot_id": s.id,
        }

    for a, s, it, cat in assigns:
        key = f"{s.col_code}-{s.row_num}"
        label = slot_display_labels.get(key) or f"{s.col_code}{s.row_num}"
        cell = cells.get(
            key,
            {
                "blocked": False,
                "entries": [],
                "cat_id": None,
                "label": label,
                "label_custom": slot_display_custom.get(key, False),
                "items": [],
                "auto_label": False,
                "slot_id": s.id,
            },
        )
        text = short_cell_text(it)
        summary = text.replace("\n", " - ")
        color = cat.color if cat else "#999"
        cell["entries"].append({
            "text": summary,
            "color": color,
            "name": auto_name_for(it),
            "description": it.description,
            "quantity": it.quantity,
            "share_drawer": bool(getattr(it, "share_drawer", False)),
            "position": label,
            "thread_size": it.thread_size,
            "main_measure": main_measure_info(it),
        })
        cell["items"].append(it)
        if cell["cat_id"] is None and it.category_id:
            cell["cat_id"] = it.category_id
        if not cell.get("label"):
            cell["label"] = label
        if cell.get("label_custom") is None:
            cell["label_custom"] = slot_display_custom.get(key, False)
        cells[key] = cell

    for anchor_key, region in merge_regions.items():
        merged_cell = {
            "blocked": False,
            "entries": [],
            "cat_id": None,
            "label": slot_display_labels.get(anchor_key) or f"{region['col_start']}{region['row_start']}",
            "label_custom": slot_display_custom.get(anchor_key, False),
            "items": [],
            "auto_label": False,
            "slot_id": slot_id_by_key.get(anchor_key),
        }
        for col, row in merge_cells_from_region(region):
            key = f"{col}-{row}"
            cell = cells.get(key)
            if cell:
                if cell.get("blocked"):
                    merged_cell["blocked"] = True
                for entry in cell.get("entries", []):
                    merged_cell["entries"].append(entry)
                    if merged_cell["cat_id"] is None:
                        merged_cell["cat_id"] = cell.get("cat_id")
                for it in cell.get("items", []):
                    merged_cell["items"].append(it)
                if merged_cell["cat_id"] is None and cell.get("cat_id"):
                    merged_cell["cat_id"] = cell.get("cat_id")
                if not merged_cell["label_custom"] and cell.get("label_custom"):
                    merged_cell["label_custom"] = True
                    if cell.get("label"):
                        merged_cell["label"] = cell["label"]
        cells[anchor_key] = merged_cell

    for cell in cells.values():
        if cell.get("blocked") or cell.get("label_custom"):
            continue
        items = cell.get("items", [])
        if items and len(items) > 1:
            auto_label = shared_drawer_label(items)
            if auto_label:
                cell["label"] = auto_label
                cell["auto_label"] = True

    return {
        "rows": rows, "cols": cols, "cells": cells,
        "cab": {"id": cab.id, "name": cab.name, "comp": cab.compartments_per_slot},
        "merge_anchors": merge_anchors,
        "merge_skips": merge_skips,
    }

@app.route("/cassettiere", methods=["GET", "POST"])
def cassettiere():
    return _placements_internal("cassettiere")

def short_cell_text(item: Item) -> str:
    lines = label_lines_for_item(item)
    return "\n".join(lines[:2])

def unified_thickness_value(item: Item):
    if item.thickness_mm is not None:
        return item.thickness_mm
    if not (is_screw(item) or is_standoff(item) or is_spacer(item)):
        return item.length_mm
    return None


@app.route("/item/<int:item_id>")
def item_view(item_id):
    """Mobile-friendly card view for QR code scans."""
    item = Item.query.get_or_404(item_id)
    a = (db.session.query(Assignment, Slot, Cabinet)
         .join(Slot, Assignment.slot_id == Slot.id)
         .join(Cabinet, Slot.cabinet_id == Cabinet.id)
         .filter(Assignment.item_id == item.id).first())
    position = slot_full_label(a[2], a[1], for_print=False) if a else None
    low_stock_threshold = 5
    custom_values = (
        db.session.query(ItemCustomFieldValue, CustomField)
        .join(CustomField, ItemCustomFieldValue.field_id == CustomField.id)
        .filter(ItemCustomFieldValue.item_id == item.id)
        .all()
    )
    return render_template(
        "item_view.html",
        item=item,
        position=position,
        low_stock_threshold=low_stock_threshold,
        custom_values=custom_values,
        can_manage_items=current_user.is_authenticated and current_user.has_permission("manage_items"),
    )

@app.route("/api/items/<int:item_id>.json")
def api_item(item_id):
    item = Item.query.get_or_404(item_id)
    a = (db.session.query(Assignment, Slot, Cabinet)
         .join(Slot, Assignment.slot_id == Slot.id)
         .join(Cabinet, Slot.cabinet_id == Cabinet.id)
         .filter(Assignment.item_id == item.id).first())
    full_pos = slot_full_label(a[2], a[1], for_print=False) if a else None
    return jsonify({
        "id": item.id,
        "name": auto_name_for(item),
        "description": item.description,
        "category": item.category.name if item.category else None,
        "category_color": item.category.color if item.category else None,
        "subtype": item.subtype.name if item.subtype else None,
        "thread_standard": item.thread_standard, "thread_size": item.thread_size,
        "length_mm": item.length_mm,
        "outer_d_mm": item.outer_d_mm,
        "inner_d_mm": item.inner_d_mm, "thickness_mm": item.thickness_mm,
        "material": item.material.name if item.material else None,
        "finish": item.finish.name if item.finish else None,
        "quantity": item.quantity,
        "position": full_pos
    })

@app.route("/api/search")
def api_search():
    q = (request.args.get("q") or "").strip()
    if len(q) < 2:
        return jsonify([])
    pattern = f"%{q}%"
    items = (
        Item.query
        .join(Item.category)
        .filter(
            or_(
                Item.name.ilike(pattern),
                Category.name.ilike(pattern),
                Item.thread_size.ilike(pattern),
                Item.description.ilike(pattern),
            )
        )
        .order_by(Item.name)
        .limit(10)
        .all()
    )
    results = []
    for item in items:
        asgn = (
            db.session.query(Assignment, Slot, Cabinet)
            .join(Slot, Assignment.slot_id == Slot.id)
            .join(Cabinet, Slot.cabinet_id == Cabinet.id)
            .filter(Assignment.item_id == item.id)
            .first()
        )
        pos = slot_full_label(asgn[2], asgn[1], for_print=False) if asgn else None
        results.append({
            "id": item.id,
            "name": auto_name_for(item),
            "category": item.category.name if item.category else None,
            "category_color": item.category.color if item.category else None,
            "quantity": item.quantity,
            "position": pos,
        })
    return jsonify(results)

@app.route("/api/slots/lookup")
def api_slot_lookup():
    cab_id = request.args.get("cabinet_id", type=int)
    col_code = (request.args.get("col_code") or "").strip().upper()
    row_num = request.args.get("row_num", type=int)
    if not (cab_id and col_code and row_num):
        return jsonify({"ok": False, "error": "Parametri mancanti."}), 400

    region = merge_region_for(cab_id, col_code, row_num)
    if region:
        col_code = region["anchor_col"]
        row_num = region["anchor_row"]
        cells = merge_cells_from_region(region)
    else:
        cells = [(col_code, row_num)]

    slots = (
        Slot.query.filter(Slot.cabinet_id == cab_id)
        .filter(or_(*[
            (Slot.col_code == col) & (Slot.row_num == row)
            for col, row in cells
        ]))
        .all()
    )
    default_label = f"{col_code}{row_num}"
    label_display = default_label
    label_print = default_label
    if slots:
        anchor_slot = next((s for s in slots if s.col_code == col_code and s.row_num == row_num), slots[0])
        label_display = slot_label(anchor_slot, for_display=True, fallback_col=col_code, fallback_row=row_num)
        label_print = slot_label(anchor_slot, for_display=False, fallback_col=col_code, fallback_row=row_num)
    else:
        return jsonify({"ok": True, "items": [], "slot_label_display": default_label, "slot_label_print": default_label, "default_label": default_label})

    slot_ids = [s.id for s in slots]
    assigns = (
        db.session.query(Assignment, Item, Category, Slot)
        .join(Item, Assignment.item_id == Item.id)
        .join(Category, Item.category_id == Category.id, isouter=True)
        .join(Slot, Assignment.slot_id == Slot.id)
        .filter(Assignment.slot_id.in_(slot_ids))
        .order_by(Slot.col_code, Slot.row_num, Assignment.compartment_no)
        .all()
    )
    items = []
    for a, it, cat, slot in assigns:
        items.append({
            "id": it.id,
            "name": auto_name_for(it),
            "category": cat.name if cat else None,
            "color": cat.color if cat else "#999999",
            "position": slot_label(slot, for_display=True, fallback_col=slot.col_code, fallback_row=slot.row_num),
        })
    return jsonify({"ok": True, "items": items})

# ===================== ADMIN: ARTICOLI =====================
@app.route("/admin")
@login_required
def admin_items():
    return _render_articles_page()

@app.route("/admin/items/export")
@login_required
def export_items_csv():
    items = Item.query.options(
        selectinload(Item.category),
        selectinload(Item.subtype),
        selectinload(Item.material),
        selectinload(Item.finish),
    ).order_by(Item.id).all()

    assignments = (
        db.session.query(Assignment.item_id, Cabinet, Slot)
        .join(Slot, Assignment.slot_id == Slot.id)
        .join(Cabinet, Slot.cabinet_id == Cabinet.id)
        .all()
    )
    pos_by_item = {
        item_id: slot_full_label(cab, slot, for_print=False)
        for item_id, cab, slot in assignments
    }

    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow([
        "id",
        "name",
        "category",
        "subtype",
        "thread_standard",
        "thread_size",
        "length_mm",
        "outer_d_mm",
        "inner_d_mm",
        "thickness_mm",
        "material",
        "finish",
        "description",
        "quantity",
        "share_drawer",
        "updated_at",
        "position",
    ])
    for item in items:
        writer.writerow([
            item.id,
            auto_name_for(item),
            item.category.name if item.category else "",
            item.subtype.name if item.subtype else "",
            item.thread_standard or "",
            item.thread_size or "",
            item.length_mm if item.length_mm is not None else "",
            item.outer_d_mm if item.outer_d_mm is not None else "",
            item.inner_d_mm if item.inner_d_mm is not None else "",
            item.thickness_mm if item.thickness_mm is not None else "",
            item.material.name if item.material else "",
            item.finish.name if item.finish else "",
            item.description or "",
            item.quantity,
            "1" if item.share_drawer else "0",
            item.updated_at.isoformat() if item.updated_at else "",
            pos_by_item.get(item.id, ""),
        ])
    output.seek(0)
    buffer = io.BytesIO(output.getvalue().encode("utf-8"))
    return send_file(buffer, as_attachment=True, download_name="articoli.csv", mimetype="text/csv")

def _serialize_records(query, fields: list[str]) -> list[dict]:
    records = []
    for obj in query:
        record = {field: getattr(obj, field) for field in fields}
        records.append(record)
    return records

@app.route("/admin/data/export.json")
@login_required
def export_data_json():
    payload = {
        "exported_at": datetime.now(timezone.utc).isoformat(),
        "categories": _serialize_records(Category.query.order_by(Category.id), ["id", "name", "color", "main_measure_mode"]),
        "materials": _serialize_records(Material.query.order_by(Material.id), ["id", "name"]),
        "finishes": _serialize_records(Finish.query.order_by(Finish.id), ["id", "name"]),
        "thread_standards": _serialize_records(ThreadStandard.query.order_by(ThreadStandard.id), ["id", "code", "label", "sort_order"]),
        "thread_sizes": _serialize_records(ThreadSize.query.order_by(ThreadSize.id), ["id", "standard_id", "value", "sort_order"]),
        "custom_fields": _serialize_records(CustomField.query.order_by(CustomField.id), ["id", "name", "field_type", "options", "unit", "sort_order", "is_active"]),
        "category_field_settings": _serialize_records(CategoryFieldSetting.query.order_by(CategoryFieldSetting.id), ["id", "category_id", "field_key", "is_enabled"]),
        "item_custom_field_values": _serialize_records(ItemCustomFieldValue.query.order_by(ItemCustomFieldValue.id), ["id", "item_id", "field_id", "value_text"]),
        "subtypes": _serialize_records(Subtype.query.order_by(Subtype.id), ["id", "category_id", "name"]),
        "locations": _serialize_records(Location.query.order_by(Location.id), ["id", "name"]),
        "cabinets": _serialize_records(Cabinet.query.order_by(Cabinet.id), ["id", "location_id", "name", "rows_max", "cols_max", "compartments_per_slot"]),
        "slots": _serialize_records(Slot.query.order_by(Slot.id), ["id", "cabinet_id", "row_num", "col_code", "is_blocked", "display_label_override", "print_label_override"]),
        "drawer_merges": _serialize_records(DrawerMerge.query.order_by(DrawerMerge.id), ["id", "cabinet_id", "row_start", "row_end", "col_start", "col_end"]),
        "items": _serialize_records(Item.query.order_by(Item.id), [
            "id", "category_id", "subtype_id", "name", "description", "share_drawer",
            "thread_standard", "thread_size", "inner_d_mm", "thickness_mm", "length_mm", "outer_d_mm",
            "material_id", "finish_id", "quantity", "label_show_category", "label_show_subtype",
            "label_show_thread", "label_show_measure", "label_show_main", "label_show_material", "updated_at"
        ]),
        "assignments": _serialize_records(Assignment.query.order_by(Assignment.id), ["id", "slot_id", "compartment_no", "item_id"]),
    }
    buffer = io.BytesIO(json.dumps(payload, ensure_ascii=False, indent=2).encode("utf-8"))
    return send_file(buffer, as_attachment=True, download_name="magazzino_data.json", mimetype="application/json")

@app.route("/admin/data/export.csv")
@login_required
def export_data_csv():
    return export_items_csv()

def _parse_bool(value: str | None) -> bool:
    if value is None:
        return False
    return str(value).strip().lower() in {"1", "true", "yes", "y", "si", "s"}

def _parse_float(value: str | None) -> float | None:
    if value is None:
        return None
    cleaned = str(value).strip()
    if cleaned == "":
        return None
    return float(cleaned)

def _find_or_create_by_name(model, name: str, **extra_fields):
    cleaned = (name or "").strip()
    if not cleaned:
        return None
    instance = model.query.filter_by(name=cleaned).first()
    if instance:
        return instance
    instance = model(name=cleaned, **extra_fields)
    db.session.add(instance)
    db.session.flush()
    return instance

def _parse_position(value: str) -> tuple[str | None, str | None, int | None]:
    cleaned = (value or "").strip()
    if not cleaned:
        return None, None, None
    if "-" not in cleaned:
        return None, None, None
    cab_name, slot_label = cleaned.rsplit("-", 1)
    cab_name = cab_name.strip()
    slot_label = slot_label.strip().upper()
    match = re.match(r"^([A-Z]{1,2})(\\d+)$", slot_label)
    if not match:
        return None, None, None
    return cab_name, match.group(1), int(match.group(2))

def _import_items_from_csv(file_storage) -> tuple[int, list[str]]:
    content = file_storage.read()
    text = content.decode("utf-8-sig")
    reader = csv.DictReader(io.StringIO(text))
    imported = 0
    warnings = []
    for row in reader:
        category = _find_or_create_by_name(Category, row.get("category") or "")
        if not category:
            warnings.append("Categoria mancante per una riga CSV.")
            continue
        subtype = None
        subtype_name = (row.get("subtype") or "").strip()
        if subtype_name:
            subtype = Subtype.query.filter_by(category_id=category.id, name=subtype_name).first()
            if not subtype:
                subtype = Subtype(category_id=category.id, name=subtype_name)
                db.session.add(subtype)
                db.session.flush()
        material = _find_or_create_by_name(Material, row.get("material") or "")
        finish = _find_or_create_by_name(Finish, row.get("finish") or "")

        item_id = None
        if row.get("id"):
            try:
                item_id = int(row["id"])
            except ValueError:
                item_id = None
        item = Item.query.get(item_id) if item_id else None
        if not item:
            item = Item(id=item_id) if item_id else Item()
            db.session.add(item)

        item.category_id = category.id
        item.subtype_id = subtype.id if subtype else None
        item.thread_standard = (row.get("thread_standard") or "").strip() or None
        item.thread_size = (row.get("thread_size") or "").strip() or None
        item.length_mm = _parse_float(row.get("length_mm"))
        item.outer_d_mm = _parse_float(row.get("outer_d_mm"))
        item.inner_d_mm = _parse_float(row.get("inner_d_mm"))
        item.thickness_mm = _parse_float(row.get("thickness_mm"))
        item.material_id = material.id if material else None
        item.finish_id = finish.id if finish else None
        item.description = (row.get("description") or "").strip() or None
        quantity_val = row.get("quantity")
        item.quantity = int(quantity_val) if quantity_val not in (None, "") else 0
        item.share_drawer = _parse_bool(row.get("share_drawer"))
        item.name = auto_name_for(item)
        db.session.flush()

        cab_name, col_code, row_num = _parse_position(row.get("position") or "")
        if cab_name and col_code and row_num:
            cabinet = Cabinet.query.filter_by(name=cab_name).first()
            if cabinet:
                try:
                    _assign_position(item, cabinet.id, col_code, row_num, force_share=True)
                except Exception as exc:
                    warnings.append(f"Posizione non assegnata per articolo {item.id}: {exc}")
            else:
                warnings.append(f"Cassettiera '{cab_name}' non trovata per articolo {item.id}.")

        imported += 1
    db.session.commit()
    return imported, warnings

def _merge_records(model, records: list[dict], fields: list[str]) -> int:
    imported = 0
    for record in records:
        if not isinstance(record, dict):
            continue
        payload = {field: record.get(field) for field in fields if field in record}
        if not payload:
            continue
        obj = model(**payload)
        db.session.merge(obj)
        imported += 1
    return imported

@app.route("/admin/data/import", methods=["POST"])
@login_required
def import_data():
    format_name = (request.form.get("format") or "").lower().strip()
    file_storage = request.files.get("file")
    if not file_storage:
        flash("Seleziona un file da importare.", "danger")
        return redirect(url_for("admin_items"))

    if format_name == "csv":
        imported, warnings = _import_items_from_csv(file_storage)
        if warnings:
            for warning in warnings[:5]:
                flash(warning, "warning")
            if len(warnings) > 5:
                flash(f"Altri {len(warnings) - 5} avvisi durante l'import.", "warning")
        flash(f"Import CSV completato: {imported} articoli.", "success")
        return redirect(url_for("admin_items"))

    if format_name == "json":
        try:
            payload = json.loads(file_storage.read().decode("utf-8"))
        except (json.JSONDecodeError, ValueError):
            flash("File JSON non valido.", "danger")
            return redirect(url_for("admin_items"))

        total = 0
        total += _merge_records(Category, payload.get("categories", []), ["id", "name", "color", "main_measure_mode"])
        total += _merge_records(Material, payload.get("materials", []), ["id", "name"])
        total += _merge_records(Finish, payload.get("finishes", []), ["id", "name"])
        total += _merge_records(ThreadStandard, payload.get("thread_standards", []), ["id", "code", "label", "sort_order"])
        total += _merge_records(ThreadSize, payload.get("thread_sizes", []), ["id", "standard_id", "value", "sort_order"])
        total += _merge_records(CustomField, payload.get("custom_fields", []), ["id", "name", "field_type", "options", "unit", "sort_order", "is_active"])
        total += _merge_records(CategoryFieldSetting, payload.get("category_field_settings", []), ["id", "category_id", "field_key", "is_enabled"])
        total += _merge_records(Subtype, payload.get("subtypes", []), ["id", "category_id", "name"])
        total += _merge_records(Location, payload.get("locations", []), ["id", "name"])
        total += _merge_records(Cabinet, payload.get("cabinets", []), ["id", "location_id", "name", "rows_max", "cols_max", "compartments_per_slot"])
        total += _merge_records(Slot, payload.get("slots", []), ["id", "cabinet_id", "row_num", "col_code", "is_blocked", "display_label_override", "print_label_override"])
        total += _merge_records(DrawerMerge, payload.get("drawer_merges", []), ["id", "cabinet_id", "row_start", "row_end", "col_start", "col_end"])
        total += _merge_records(Item, payload.get("items", []), [
            "id", "category_id", "subtype_id", "name", "description", "share_drawer",
            "thread_standard", "thread_size", "inner_d_mm", "thickness_mm", "length_mm", "outer_d_mm",
            "material_id", "finish_id", "quantity", "label_show_category", "label_show_subtype",
            "label_show_thread", "label_show_measure", "label_show_main", "label_show_material", "updated_at"
        ])
        total += _merge_records(ItemCustomFieldValue, payload.get("item_custom_field_values", []), ["id", "item_id", "field_id", "value_text"])
        total += _merge_records(Assignment, payload.get("assignments", []), ["id", "slot_id", "compartment_no", "item_id"])
        db.session.commit()
        flash(f"Import JSON completato: {total} record.", "success")
        return redirect(url_for("admin_items"))

    flash("Formato import non supportato.", "danger")
    return redirect(url_for("admin_items"))


@app.route("/admin/to_place")
@login_required
def to_place():
    return redirect(url_for("placements"))

@app.route("/admin/items/add", methods=["POST"])
@login_required
def add_item():
    f = request.form
    try:
        category_id = int(f.get("category_id"))
    except Exception:
        flash("Categoria non valida.", "danger")
        return redirect(url_for("admin_items"))
    category = Category.query.get_or_404(category_id)
    try:
        length_mm, thickness_mm = split_main_measure_for_category(category, f.get("length_mm"))
    except ValueError:
        flash("Valore Lunghezza/Spessore non valido.", "danger")
        return redirect(url_for("admin_items"))
    item = Item(
        description=f.get("description") or None,
        category_id=category.id,
        subtype_id=int(f.get("subtype_id")) if f.get("subtype_id") else None,
        thread_standard=f.get("thread_standard") or None,
        thread_size=f.get("thread_size") or None,
        length_mm=length_mm,
        outer_d_mm=float(f.get("outer_d_mm")) if f.get("outer_d_mm") else None,
        inner_d_mm=float(f.get("inner_d_mm")) if f.get("inner_d_mm") else None,
        thickness_mm=thickness_mm,
        material_id=int(f.get("material_id")) if f.get("material_id") else None,
        finish_id=int(f.get("finish_id")) if f.get("finish_id") else None,
        quantity=int(f.get("quantity")) if f.get("quantity") else 0,
        share_drawer=bool(f.get("share_drawer")),
        label_show_category=bool(f.get("label_show_category")),
        label_show_subtype =bool(f.get("label_show_subtype")),
        label_show_thread  =bool(f.get("label_show_thread")),
        label_show_measure =bool(f.get("label_show_measure")),
        label_show_main    =bool(f.get("label_show_main")),
        label_show_material=bool(f.get("label_show_material")),
        updated_at=datetime.utcnow(),
    )
    item.name = auto_name_for(item)
    db.session.add(item); db.session.flush()
    save_custom_field_values(item, f)
    cab_id  = f.get("cabinet_id"); row_num = f.get("row_num"); col_code = f.get("col_code")
    if cab_id and row_num and col_code:
        _assign_position(item, int(cab_id), col_code, int(row_num))
    db.session.commit()
    flash("Articolo aggiunto", "success")
    keep_params = {
        "keep_category_id": item.category_id,
        "keep_material_id": item.material_id,
        "keep_finish_id": item.finish_id,
        "keep_description": item.description or "",
        "keep_thread_size": item.thread_size or "",
    }
    keep_params = {k: v for k, v in keep_params.items() if v not in (None, "")}
    return redirect(url_for("admin_items", **keep_params))

@app.route("/admin/items/<int:item_id>/edit", methods=["GET","POST"])
@login_required
def edit_item(item_id):
    item = Item.query.get_or_404(item_id)
    next_url = _safe_next_url(request.values.get("next"))
    if request.method == "POST":
        f = request.form
        try:
            category_id = int(f.get("category_id"))
            category = Category.query.get_or_404(category_id)
            length_mm, thickness_mm = split_main_measure_for_category(category, f.get("length_mm"))
        except ValueError:
            flash("Valore Lunghezza/Spessore non valido.", "danger")
            return redirect(url_for("edit_item", item_id=item.id))
        item.description = f.get("description") or None
        item.category_id = category.id
        item.subtype_id = int(f.get("subtype_id")) if f.get("subtype_id") else None
        item.thread_standard = f.get("thread_standard") or None
        item.thread_size = f.get("thread_size") or None
        item.length_mm = length_mm
        item.outer_d_mm = float(f.get("outer_d_mm")) if f.get("outer_d_mm") else None
        item.inner_d_mm = float(f.get("inner_d_mm")) if f.get("inner_d_mm") else None
        item.thickness_mm = thickness_mm
        item.material_id = int(f.get("material_id")) if f.get("material_id") else None
        item.finish_id = int(f.get("finish_id")) if f.get("finish_id") else None
        item.quantity = int(f.get("quantity")) if f.get("quantity") else 0
        item.share_drawer = bool(f.get("share_drawer"))
        item.label_show_category = bool(f.get("label_show_category"))
        item.label_show_subtype  = bool(f.get("label_show_subtype"))
        item.label_show_thread   = bool(f.get("label_show_thread"))
        item.label_show_measure  = bool(f.get("label_show_measure"))
        item.label_show_main     = bool(f.get("label_show_main"))
        item.label_show_material = bool(f.get("label_show_material"))
        item.updated_at = datetime.utcnow()
        item.name = auto_name_for(item)
        save_custom_field_values(item, f)
        db.session.commit()
        flash("Articolo aggiornato", "success")
        if next_url:
            return redirect(url_for("edit_item", item_id=item.id, next=next_url))
        return redirect(url_for("edit_item", item_id=item.id))

    categories = Category.query.order_by(Category.name).all()
    subtypes   = Subtype.query.order_by(Subtype.name).all()
    materials  = Material.query.order_by(Material.name).all()
    finishes   = Finish.query.order_by(Finish.name).all()
    cabinets   = Cabinet.query.order_by(Cabinet.name).all()

    subtypes_by_cat = {}
    for s in subtypes:
        subtypes_by_cat.setdefault(s.category_id, []).append({"id": s.id, "name": s.name})

    thread_standards, sizes_by_standard = load_form_options()

    pos = (db.session.query(Assignment, Slot, Cabinet)
           .join(Slot, Assignment.slot_id == Slot.id)
           .join(Cabinet, Slot.cabinet_id == Cabinet.id)
           .filter(Assignment.item_id == item.id).first())
    current_cabinet_id = pos[2].id if pos else None
    current_col_code = pos[1].col_code if pos else ""
    current_row_num = pos[1].row_num if pos else ""

    custom_fields = CustomField.query.filter_by(is_active=True).order_by(CustomField.sort_order, CustomField.name).all()
    serialized_custom_fields = serialize_custom_fields(custom_fields)
    custom_field_values = {
        val.field_id: (val.value_text or "")
        for val in ItemCustomFieldValue.query.filter_by(item_id=item.id).all()
    }
    category_fields = build_category_field_map(categories)
    measure_labels = build_measure_labels(categories)

    return render_template("admin/edit_item.html",
        item=item, categories=categories, materials=materials, finishes=finishes,
        cabinets=cabinets, subtypes_by_cat=subtypes_by_cat,
        thread_standards=thread_standards, sizes_by_standard=sizes_by_standard,
        custom_fields=serialized_custom_fields,
        custom_field_values=custom_field_values,
        category_fields=category_fields,
        measure_labels=measure_labels,
        current_cabinet_id=current_cabinet_id,
        current_col_code=current_col_code,
        current_row_num=current_row_num,
        next_url=next_url,
    )

@app.route("/admin/items/<int:item_id>/delete", methods=["POST"])
@login_required
def delete_item(item_id):
    item = Item.query.get_or_404(item_id)
    Assignment.query.filter_by(item_id=item.id).delete()
    db.session.delete(item)
    db.session.commit()
    flash("Articolo eliminato", "success")
    next_url = _safe_next_url(request.values.get("next"))
    if next_url:
        return redirect(next_url)
    return redirect(url_for("admin_items"))

# ---- Posizione item ----
def _load_slot_assignments(slot_id: int, ignore_item_id: int | None = None):
    assigns = Assignment.query.filter_by(slot_id=slot_id).all()
    filtered = [a for a in assigns if a.item_id != ignore_item_id]
    item_ids = [a.item_id for a in filtered]
    items = Item.query.filter(Item.id.in_(item_ids)).all() if item_ids else []
    return assigns, items

def _normalize_thread_size(val: Optional[str]) -> str:
    return (val or "").strip().lower()

class SharePermissionError(RuntimeError):
    def __init__(self, items: list[Item]):
        super().__init__("Il cassetto contiene articoli che non supportano la condivisione.")
        self.items = items

def _share_slot_status(existing_items: list[Item], new_item: Item):
    if not existing_items:
        return True, []
    measure_new = _normalize_thread_size(getattr(new_item, "thread_size", None))
    category_new = getattr(new_item, "category_id", None)
    measures_ok = all(_normalize_thread_size(getattr(it, "thread_size", None)) == measure_new for it in existing_items)
    categories_ok = all(getattr(it, "category_id", None) == category_new for it in existing_items)
    # Permetti la condivisione se categoria e misura coincidono (comportamento precedente)
    # oppure se tutti condividono la stessa misura (es. M10) anche con categorie diverse.
    if not ((categories_ok and measures_ok) or (measure_new and measures_ok)):
        return False, []
    blockers = [it for it in existing_items if not getattr(it, "share_drawer", False)]
    if not getattr(new_item, "share_drawer", False):
        blockers.append(new_item)
    if blockers:
        return False, blockers
    return True, []

def _can_share_slot(existing_items: list[Item], new_item: Item) -> bool:
    ok, _ = _share_slot_status(existing_items, new_item)
    return ok

def _assign_position(item, cabinet_id:int, col_code:str, row_num:int, *, force_share: bool = False):
    if not column_code_valid(col_code):         raise ValueError("Colonna non valida (A..Z o AA..ZZ).")
    if not (1 <= int(row_num) <= 128):          raise ValueError("Riga non valida (1..128).")
    anchor_slot, slots, assignments, slot_items = _collect_region_assignments(
        cabinet_id, col_code, row_num, ignore_item_id=item.id
    )
    if anchor_slot.is_blocked:                         raise RuntimeError("La cella è bloccata (non assegnabile).")
    Assignment.query.filter_by(item_id=item.id).delete()

    can_share, blockers = _share_slot_status(slot_items, item)
    if not can_share:
        if blockers and force_share:
            for it in blockers:
                it.share_drawer = True
        elif blockers:
            raise SharePermissionError(blockers)
        else:
            raise RuntimeError("Il cassetto contiene articoli che non supportano la condivisione.")

    cab = db.session.get(Cabinet, int(cabinet_id))
    max_comp = _max_compartments_for_slot(cab, anchor_slot.col_code, anchor_slot.row_num)
    if len(assignments) >= max_comp:
        raise RuntimeError("Nessuno scomparto libero nello slot scelto.")

    # Sposta tutti gli assignment della regione nello slot anchor e riassegna i comparti.
    for a in assignments:
        a.slot_id = anchor_slot.id
    db.session.add(Assignment(slot_id=anchor_slot.id, compartment_no=0, item_id=item.id))
    _reassign_compartments(anchor_slot.id, cab)

def _suggest_position(item: Item):
    rows = (
        db.session.query(
            Slot,
            Cabinet,
            func.count(Assignment.id).label("assign_count"),
            func.min(Item.category_id).label("min_cat"),
            func.max(Item.category_id).label("max_cat"),
        )
        .join(Cabinet, Slot.cabinet_id == Cabinet.id)
        .outerjoin(Assignment, Assignment.slot_id == Slot.id)
        .outerjoin(Item, Assignment.item_id == Item.id)
        .group_by(Slot.id, Cabinet.id)
        .order_by(Cabinet.name, Slot.col_code, Slot.row_num)
        .all()
    )
    for slot, cab, assign_count, min_cat, max_cat in rows:
        if slot.is_blocked or assign_count == 0:
            continue
        _, slot_items = _load_slot_assignments(slot.id)
        if not _can_share_slot(slot_items, item):
            continue
        max_comp = _max_compartments_for_slot(cab, slot.col_code, slot.row_num)
        if assign_count < max_comp:
            return cab.id, slot.col_code, slot.row_num
    return None

@app.route("/admin/items/<int:item_id>/suggest_position")
@login_required
def suggest_position(item_id):
    item = Item.query.get_or_404(item_id)
    sug = _suggest_position(item)
    if not sug:
        return jsonify({"ok": False, "error": "Nessuna posizione compatibile trovata dove la categoria è già presente."})
    cab_id, col_code, row_num = sug
    return jsonify({"ok": True, "cabinet_id": cab_id, "col_code": col_code, "row_num": row_num})

@app.route("/admin/items/<int:item_id>/set_position", methods=["POST"])
@login_required
def set_position(item_id):
    item = Item.query.get_or_404(item_id)
    cab_id  = request.form.get("cabinet_id")
    row_num = request.form.get("row_num")
    col_code= request.form.get("col_code")
    force_share = bool(request.form.get("force_share"))
    if not (cab_id and row_num and col_code):
        flash("Compila cabinet, riga e colonna.", "danger"); return redirect(url_for("edit_item", item_id=item.id))
    try:
        _assign_position(item, int(cab_id), col_code, int(row_num), force_share=force_share)
        db.session.commit()
        flash("Posizione aggiornata.", "success")
    except SharePermissionError as e:
        db.session.rollback()
        blocker_names = ", ".join(sorted({auto_name_for(it) for it in e.items}))
        flash(f"Il cassetto contiene articoli che non supportano la condivisione: {blocker_names}.", "danger")
    except Exception as e:
        db.session.rollback(); flash(str(e), "danger")
    return redirect(url_for("edit_item", item_id=item.id))

@app.route("/admin/items/<int:item_id>/set_position.json", methods=["POST"])
@login_required
def set_position_json(item_id):
    item = Item.query.get_or_404(item_id)
    cab_id  = request.form.get("cabinet_id")
    row_num = request.form.get("row_num")
    col_code= request.form.get("col_code")
    force_share = bool(request.form.get("force_share"))
    if not (cab_id and row_num and col_code):
        return jsonify({"ok": False, "error": "Compila cabinet, riga e colonna."}), 400
    try:
        _assign_position(item, int(cab_id), col_code, int(row_num), force_share=force_share)
        db.session.commit()
        return jsonify({"ok": True})
    except SharePermissionError as e:
        db.session.rollback()
        blockers = [{"id": it.id, "name": auto_name_for(it)} for it in e.items]
        return jsonify({"ok": False, "error": str(e), "share_blockers": blockers}), 409
    except Exception as e:
        db.session.rollback()
        return jsonify({"ok": False, "error": str(e)}), 400

@app.route("/admin/items/<int:item_id>/clear_position", methods=["POST"])
@login_required
def clear_position(item_id):
    Assignment.query.filter_by(item_id=item_id).delete()
    db.session.commit()
    flash("Posizione rimossa.", "success")
    return redirect(url_for("edit_item", item_id=item_id))

@app.route("/admin/items/<int:item_id>/move_slot", methods=["POST"])
@login_required
def move_item_slot(item_id):
    item = Item.query.get_or_404(item_id)
    cab_to  = request.form.get("cabinet_id")
    col_to  = (request.form.get("col_code") or "").strip().upper()
    row_to  = request.form.get("row_num")
    if not (cab_to and col_to and row_to):
        flash("Compila cabinet, riga e colonna per spostare il cassetto.", "danger")
        return redirect(url_for("edit_item", item_id=item.id))
    try:
        cab_to = int(cab_to)
        row_to = int(row_to)
    except Exception:
        flash("Coordinate destinazione non valide.", "danger")
        return redirect(url_for("edit_item", item_id=item.id))

    assign = Assignment.query.filter_by(item_id=item.id).first()
    if not assign:
        flash("Questo articolo non ha una posizione da spostare.", "warning")
        return redirect(url_for("edit_item", item_id=item.id))
    src_slot = db.session.get(Slot, assign.slot_id)
    if not src_slot:
        flash("Slot origine non trovato.", "danger")
        return redirect(url_for("edit_item", item_id=item.id))

    region_from = merge_region_for(src_slot.cabinet_id, src_slot.col_code, src_slot.row_num)
    if region_from:
        anchor_col = region_from["anchor_col"]
        anchor_row = region_from["anchor_row"]
        src_slot = Slot.query.filter_by(cabinet_id=src_slot.cabinet_id, col_code=anchor_col, row_num=anchor_row).first() or _ensure_slot(src_slot.cabinet_id, anchor_col, anchor_row)

    region_to = merge_region_for(cab_to, col_to, row_to)
    if region_to:
        col_to = region_to["anchor_col"]
        row_to = region_to["anchor_row"]

    dst_slot = _ensure_slot(cab_to, col_to, row_to)
    if dst_slot.is_blocked:
        flash("La destinazione è bloccata.", "danger")
        return redirect(url_for("edit_item", item_id=item.id))
    if src_slot.is_blocked:
        flash("Il cassetto origine è bloccato: impossibile spostare.", "danger")
        return redirect(url_for("edit_item", item_id=item.id))

    src_assigns = Assignment.query.filter_by(slot_id=src_slot.id).all()
    dst_assigns = Assignment.query.filter_by(slot_id=dst_slot.id).all()
    if not src_assigns:
        flash("Nessun contenuto da spostare nel cassetto corrente.", "warning")
        return redirect(url_for("edit_item", item_id=item.id))

    src_cats = _slot_categories(src_slot.id)
    dst_cats = _slot_categories(dst_slot.id)
    if dst_assigns and (src_cats and dst_cats) and (list(src_cats)[0] != list(dst_cats)[0]):
        flash("Le categorie dei cassetti non coincidono.", "danger")
        return redirect(url_for("edit_item", item_id=item.id))

    cab_to_obj = db.session.get(Cabinet, cab_to)
    if not cab_to_obj:
        flash("Cassettiera destinazione non trovata.", "danger")
        return redirect(url_for("edit_item", item_id=item.id))
    if not _slot_capacity_ok(cab_to_obj, len(dst_assigns) + len(src_assigns), dst_slot.col_code, dst_slot.row_num):
        flash("Scomparti insufficienti nel cassetto destinazione.", "danger")
        return redirect(url_for("edit_item", item_id=item.id))

    _move_slot_assignments(src_slot, dst_slot, cab_to_obj, move_labels=True)
    db.session.commit()
    flash("Cassetto spostato.", "success")
    return redirect(url_for("edit_item", item_id=item.id))

def _admin_config_url(anchor=None):
    base = url_for("admin_config")
    return f"{base}#{anchor}" if anchor else base

# ===================== ADMIN: CATEGORIE =====================
@app.route("/admin/categories")
@login_required
def admin_categories():
    return redirect(_admin_config_url("categorie"))

@app.route("/admin/categories/add", methods=["POST"])
@login_required
def add_category():
    name = request.form.get("name","").strip()
    color = request.form.get("color","#000000").strip()
    mode = (request.form.get("main_measure_mode","") or MAIN_MEASURE_DEFAULT).strip().lower()
    if mode not in VALID_MEASURE_MODES:
        mode = MAIN_MEASURE_DEFAULT
    if len(name) < 2: return _flash_back("Nome categoria troppo corto.", "danger", "admin_config", "categorie")
    if Category.query.filter_by(name=name).first(): return _flash_back("Categoria già esistente.", "danger", "admin_config", "categorie")
    db.session.add(Category(name=name, color=color, main_measure_mode=mode)); db.session.commit()
    flash("Categoria aggiunta.", "success"); return redirect(_admin_config_url("categorie"))

@app.route("/admin/categories/<int:cat_id>/update", methods=["POST"])
@login_required
def update_category(cat_id):
    cat = Category.query.get_or_404(cat_id)
    new_name = request.form.get("name","").strip()
    new_color = request.form.get("color","#000000").strip()
    new_mode = request.form.get("main_measure_mode","").strip().lower()
    if new_mode not in VALID_MEASURE_MODES:
        new_mode = measure_mode_for_category(cat)
    if new_name and new_name != cat.name:
        if Category.query.filter(Category.id != cat.id, Category.name == new_name).first():
            return _flash_back("Esiste già una categoria con questo nome.", "danger", "admin_config", "categorie")
        cat.name = new_name
    cat.color = new_color or cat.color
    cat.main_measure_mode = new_mode
    db.session.commit()
    flash("Categoria aggiornata.", "success"); return redirect(_admin_config_url("categorie"))

@app.route("/admin/categories/<int:cat_id>/delete", methods=["POST"])
@login_required
def delete_category(cat_id):
    cat = Category.query.get_or_404(cat_id)
    used = Item.query.filter_by(category_id=cat.id).first()
    if used:
        flash("Impossibile eliminare: ci sono articoli associati.", "danger")
    else:
        db.session.delete(cat); db.session.commit(); flash("Categoria eliminata.", "success")
    return redirect(_admin_config_url("categorie"))

def _flash_back(msg, kind, endpoint, anchor=None):
    flash(msg, kind)
    url = url_for(endpoint)
    if anchor:
        url = f"{url}#{anchor}"
    return redirect(url)

@app.route("/admin/subtypes/add", methods=["POST"])
@login_required
def add_subtype():
    name = (request.form.get("name") or "").strip()
    try:
        category_id = int(request.form.get("category_id") or 0)
    except Exception:
        category_id = 0

    if category_id <= 0:
        return _flash_back("Seleziona una categoria valida per il sottotipo.", "danger", "admin_config", "sottotipi")
    if len(name) < 2:
        return _flash_back("Nome sottotipo troppo corto.", "danger", "admin_config", "sottotipi")

    # univoco per categoria (rispetta il vincolo uq_subtype_per_category)
    exists = Subtype.query.filter_by(category_id=category_id, name=name).first()
    if exists:
        return _flash_back("Esiste già un sottotipo con questo nome per la categoria selezionata.", "danger", "admin_config", "sottotipi")

    db.session.add(Subtype(category_id=category_id, name=name))
    db.session.commit()
    flash("Sottotipo aggiunto.", "success")
    return redirect(_admin_config_url("sottotipi"))


@app.route("/admin/subtypes/<int:st_id>/update", methods=["POST"])
@login_required
def update_subtype(st_id):
    st = Subtype.query.get_or_404(st_id)
    name = (request.form.get("name") or "").strip()
    try:
        category_id = int(request.form.get("category_id") or st.category_id)
    except Exception:
        category_id = st.category_id

    if len(name) < 2:
        return _flash_back("Nome sottotipo troppo corto.", "danger", "admin_config", "sottotipi")

    # evita duplicati nella stessa categoria
    clash = (
        Subtype.query
        .filter(Subtype.id != st.id,
                Subtype.category_id == category_id,
                Subtype.name == name)
        .first()
    )
    if clash:
        return _flash_back("Esiste già un sottotipo con questo nome per la categoria selezionata.", "danger", "admin_config", "sottotipi")

    st.name = name
    st.category_id = category_id
    db.session.commit()
    flash("Sottotipo aggiornato.", "success")
    return redirect(_admin_config_url("sottotipi"))


@app.route("/admin/subtypes/<int:st_id>/delete", methods=["POST"])
@login_required
def delete_subtype(st_id):
    st = Subtype.query.get_or_404(st_id)
    used = Item.query.filter_by(subtype_id=st.id).first()
    if used:
        flash("Impossibile eliminare: ci sono articoli associati a questo sottotipo.", "danger")
    else:
        db.session.delete(st)
        db.session.commit()
        flash("Sottotipo eliminato.", "success")
    return redirect(_admin_config_url("sottotipi"))

@app.route("/admin/materials/add", methods=["POST"])
@login_required
def add_material():
    name = (request.form.get("name") or "").strip()
    if len(name) < 2:
        return _flash_back("Nome materiale troppo corto.", "danger", "admin_config", "materiali")
    if Material.query.filter_by(name=name).first():
        return _flash_back("Materiale già esistente.", "danger", "admin_config", "materiali")

    db.session.add(Material(name=name))
    db.session.commit()
    flash("Materiale aggiunto.", "success")
    return redirect(_admin_config_url("materiali"))


@app.route("/admin/materials/<int:mat_id>/update", methods=["POST"])
@login_required
def update_material(mat_id):
    mat = Material.query.get_or_404(mat_id)
    name = (request.form.get("name") or "").strip()
    if len(name) < 2:
        return _flash_back("Nome materiale troppo corto.", "danger", "admin_config", "materiali")
    if Material.query.filter(Material.id != mat.id, Material.name == name).first():
        return _flash_back("Esiste già un materiale con questo nome.", "danger", "admin_config", "materiali")

    mat.name = name
    db.session.commit()
    flash("Materiale aggiornato.", "success")
    return redirect(_admin_config_url("materiali"))


@app.route("/admin/materials/<int:mat_id>/delete", methods=["POST"])
@login_required
def delete_material(mat_id):
    mat = Material.query.get_or_404(mat_id)
    used = Item.query.filter_by(material_id=mat.id).first()
    if used:
        flash("Impossibile eliminare: ci sono articoli che usano questo materiale.", "danger")
    else:
        db.session.delete(mat)
        db.session.commit()
        flash("Materiale eliminato.", "success")
    return redirect(_admin_config_url("materiali"))

@app.route("/admin/finishes/add", methods=["POST"])
@login_required
def add_finish():
    name = (request.form.get("name") or "").strip()
    if len(name) < 2:
        return _flash_back("Nome finitura troppo corto.", "danger", "admin_config", "finiture")
    if Finish.query.filter_by(name=name).first():
        return _flash_back("Finitura già esistente.", "danger", "admin_config", "finiture")

    db.session.add(Finish(name=name))
    db.session.commit()
    flash("Finitura aggiunta.", "success")
    return redirect(_admin_config_url("finiture"))


@app.route("/admin/finishes/<int:fin_id>/update", methods=["POST"])
@login_required
def update_finish(fin_id):
    fin = Finish.query.get_or_404(fin_id)
    name = (request.form.get("name") or "").strip()
    if len(name) < 2:
        return _flash_back("Nome finitura troppo corto.", "danger", "admin_config", "finiture")
    if Finish.query.filter(Finish.id != fin.id, Finish.name == name).first():
        return _flash_back("Esiste già una finitura con questo nome.", "danger", "admin_config", "finiture")

    fin.name = name
    db.session.commit()
    flash("Finitura aggiornata.", "success")
    return redirect(_admin_config_url("finiture"))


@app.route("/admin/finishes/<int:fin_id>/delete", methods=["POST"])
@login_required
def delete_finish(fin_id):
    fin = Finish.query.get_or_404(fin_id)
    used = Item.query.filter_by(finish_id=fin.id).first()
    if used:
        flash("Impossibile eliminare: ci sono articoli che usano questa finitura.", "danger")
    else:
        db.session.delete(fin)
        db.session.commit()
        flash("Finitura eliminata.", "success")
    return redirect(_admin_config_url("finiture"))

# ===================== ADMIN: CONFIGURAZIONE =====================
@app.route("/admin/config")
@login_required
def admin_config():
    ensure_category_columns()
    locations = Location.query.order_by(Location.name).all()
    cabinets  = db.session.query(Cabinet, Location).join(Location, Cabinet.location_id==Location.id).order_by(Cabinet.name).all()
    drawer_merges = (
        db.session.query(DrawerMerge, Cabinet)
        .join(Cabinet, DrawerMerge.cabinet_id == Cabinet.id)
        .order_by(Cabinet.name, DrawerMerge.row_start, DrawerMerge.col_start)
        .all()
    )
    categories = Category.query.order_by(Category.name).all()
    materials  = Material.query.order_by(Material.name).all()
    finishes   = Finish.query.order_by(Finish.name).all()
    subtypes   = (
        db.session.query(Subtype, Category)
        .join(Category, Subtype.category_id == Category.id)
        .order_by(Category.name, Subtype.name)
        .all()
    )
    used_subtypes = {
        subtype_id
        for (subtype_id,) in db.session.query(Item.subtype_id)
        .filter(Item.subtype_id.isnot(None))
        .distinct()
        .all()
    }
    used_materials = {
        material_id
        for (material_id,) in db.session.query(Item.material_id)
        .filter(Item.material_id.isnot(None))
        .distinct()
        .all()
    }
    used_finishes = {
        finish_id
        for (finish_id,) in db.session.query(Item.finish_id)
        .filter(Item.finish_id.isnot(None))
        .distinct()
        .all()
    }
    used_categories = {
        cat_id
        for (cat_id,) in db.session.query(Item.category_id)
        .filter(Item.category_id.isnot(None))
        .distinct()
        .all()
    }
    custom_fields = CustomField.query.order_by(CustomField.sort_order, CustomField.name).all()
    serialized_custom_fields = serialize_custom_fields(custom_fields)
    field_defs = build_field_definitions(serialized_custom_fields)
    category_fields = build_category_field_map(categories)
    used_category_fields = get_used_field_keys_by_category()
    users = User.query.order_by(User.username).all()
    roles = Role.query.order_by(Role.name).all()
    permissions = Permission.query.order_by(Permission.label).all()
    can_manage_config = current_user.has_permission("manage_config")
    can_manage_users = current_user.has_permission("manage_users")
    can_manage_roles = current_user.has_permission("manage_roles")
    return render_template(
        "admin/config.html",
        locations=locations,
        cabinets=cabinets,
        drawer_merges=drawer_merges,
        settings=get_settings(),
        mqtt_settings=get_mqtt_settings(),
        categories=categories,
        materials=materials,
        finishes=finishes,
        subtypes=subtypes,
        used_subtypes=used_subtypes,
        used_materials=used_materials,
        used_finishes=used_finishes,
        used_categories=used_categories,
        custom_fields=serialized_custom_fields,
        field_defs=field_defs,
        category_fields=category_fields,
        used_category_fields=used_category_fields,
        users=users,
        roles=roles,
        permissions=permissions,
        page_format_options=PAGE_FORMAT_OPTIONS,
        can_manage_config=can_manage_config,
        can_manage_users=can_manage_users,
        can_manage_roles=can_manage_roles,
    )

@app.route("/admin/users/<int:user_id>/role", methods=["POST"])
@login_required
def update_user_role(user_id):
    user = User.query.get_or_404(user_id)
    role_id = request.form.get("role_id", type=int)
    role = Role.query.get(role_id)
    if not role:
        return _flash_back("Ruolo non valido.", "danger", "admin_config", "utenti")
    if user.id == current_user.id and not any(p.key == "manage_users" for p in role.permissions):
        return _flash_back("Non puoi rimuovere i permessi di gestione utenti dal tuo account.", "danger", "admin_config", "utenti")
    if user.has_permission("manage_users") and not any(p.key == "manage_users" for p in role.permissions):
        remaining_admins = users_with_permission("manage_users").filter(User.id != user.id).count()
        if remaining_admins == 0:
            return _flash_back("Deve esistere almeno un amministratore.", "danger", "admin_config", "utenti")
    user.role = role
    db.session.commit()
    flash("Ruolo utente aggiornato.", "success")
    return redirect(_admin_config_url("utenti"))

@app.route("/admin/roles/add", methods=["POST"])
@login_required
def add_role():
    name = (request.form.get("name") or "").strip()
    description = (request.form.get("description") or "").strip() or None
    if len(name) < 2:
        return _flash_back("Nome ruolo troppo corto.", "danger", "admin_config", "ruoli")
    if Role.query.filter_by(name=name).first():
        return _flash_back("Esiste già un ruolo con questo nome.", "danger", "admin_config", "ruoli")
    role = Role(name=name, description=description, is_system=False)
    db.session.add(role)
    db.session.commit()
    flash("Ruolo creato.", "success")
    return redirect(_admin_config_url("ruoli"))

@app.route("/admin/roles/<int:role_id>/update", methods=["POST"])
@login_required
def update_role(role_id):
    role = Role.query.get_or_404(role_id)
    name = (request.form.get("name") or "").strip()
    description = (request.form.get("description") or "").strip() or None
    permission_keys = set(request.form.getlist("permission_keys"))

    if len(name) < 2:
        return _flash_back("Nome ruolo troppo corto.", "danger", "admin_config", "ruoli")
    existing = Role.query.filter(Role.id != role.id, Role.name == name).first()
    if existing:
        return _flash_back("Esiste già un ruolo con questo nome.", "danger", "admin_config", "ruoli")
    if role.id == current_user.role_id and "manage_users" not in permission_keys:
        return _flash_back("Non puoi rimuovere la gestione utenti dal tuo ruolo.", "danger", "admin_config", "ruoli")
    if "manage_users" not in permission_keys:
        remaining_admins = users_with_permission("manage_users").filter(User.role_id != role.id).count()
        if remaining_admins == 0 and role.users:
            return _flash_back("Deve esistere almeno un amministratore.", "danger", "admin_config", "ruoli")

    role.name = name
    role.description = description
    permissions = Permission.query.filter(Permission.key.in_(permission_keys)).all() if permission_keys else []
    role.permissions = permissions
    db.session.commit()
    flash("Ruolo aggiornato.", "success")
    return redirect(_admin_config_url("ruoli"))

@app.route("/admin/roles/<int:role_id>/delete", methods=["POST"])
@login_required
def delete_role(role_id):
    role = Role.query.get_or_404(role_id)
    if role.is_system:
        return _flash_back("Impossibile eliminare un ruolo di sistema.", "danger", "admin_config", "ruoli")
    if role.users:
        return _flash_back("Impossibile eliminare: ci sono utenti associati.", "danger", "admin_config", "ruoli")
    db.session.delete(role)
    db.session.commit()
    flash("Ruolo eliminato.", "success")
    return redirect(_admin_config_url("ruoli"))

@app.route("/admin/permissions/add", methods=["POST"])
@login_required
def add_permission():
    key = (request.form.get("key") or "").strip().lower().replace(" ", "_")
    label = (request.form.get("label") or "").strip()
    description = (request.form.get("description") or "").strip() or None
    if len(key) < 3 or not all(ch.isalnum() or ch in {"_", "-"} for ch in key):
        return _flash_back("Chiave permesso non valida.", "danger", "admin_config", "permessi")
    if len(label) < 3:
        return _flash_back("Etichetta permesso troppo corta.", "danger", "admin_config", "permessi")
    if Permission.query.filter_by(key=key).first():
        return _flash_back("Esiste già un permesso con questa chiave.", "danger", "admin_config", "permessi")
    db.session.add(Permission(key=key, label=label, description=description, is_system=False))
    db.session.commit()
    flash("Permesso creato.", "success")
    return redirect(_admin_config_url("permessi"))

@app.route("/admin/config/fields/<int:cat_id>/update", methods=["POST"])
@login_required
def update_category_fields(cat_id):
    category = Category.query.get_or_404(cat_id)
    selected_keys = set(request.form.getlist("field_keys"))
    used_fields = get_used_field_keys_by_category().get(category.id, [])
    selected_keys.update(used_fields)
    CategoryFieldSetting.query.filter_by(category_id=category.id).delete()
    if not selected_keys:
        db.session.add(CategoryFieldSetting(category_id=category.id, field_key="__none__", is_enabled=False))
    else:
        for key in sorted(selected_keys):
            db.session.add(CategoryFieldSetting(category_id=category.id, field_key=key, is_enabled=True))
    db.session.commit()
    flash(f"Campi aggiornati per {category.name}.", "success")
    return redirect(_admin_config_url("campi-categoria"))

@app.route("/admin/custom_fields/add", methods=["POST"])
@login_required
def add_custom_field():
    name = (request.form.get("name") or "").strip()
    field_type = (request.form.get("field_type") or "text").strip().lower()
    options = (request.form.get("options") or "").strip() or None
    unit = (request.form.get("unit") or "").strip() or None
    sort_order = int(request.form.get("sort_order") or 0)
    is_active = bool(request.form.get("is_active"))
    if len(name) < 2:
        return _flash_back("Nome campo troppo corto.", "danger", "admin_config")
    if field_type not in {"text", "number", "select"}:
        return _flash_back("Tipo campo non valido.", "danger", "admin_config")
    if CustomField.query.filter_by(name=name).first():
        return _flash_back("Campo personalizzato già esistente.", "danger", "admin_config")
    db.session.add(CustomField(
        name=name,
        field_type=field_type,
        options=options,
        unit=unit,
        sort_order=sort_order,
        is_active=is_active,
    ))
    db.session.commit()
    flash("Campo personalizzato aggiunto.", "success")
    return redirect(url_for("admin_config"))

@app.route("/admin/custom_fields/<int:field_id>/update", methods=["POST"])
@login_required
def update_custom_field(field_id):
    field = CustomField.query.get_or_404(field_id)
    name = (request.form.get("name") or "").strip()
    field_type = (request.form.get("field_type") or "text").strip().lower()
    options = (request.form.get("options") or "").strip() or None
    unit = (request.form.get("unit") or "").strip() or None
    sort_order = int(request.form.get("sort_order") or 0)
    is_active = bool(request.form.get("is_active"))
    if len(name) < 2:
        return _flash_back("Nome campo troppo corto.", "danger", "admin_config")
    if field_type not in {"text", "number", "select"}:
        return _flash_back("Tipo campo non valido.", "danger", "admin_config")
    if CustomField.query.filter(CustomField.id != field.id, CustomField.name == name).first():
        return _flash_back("Esiste già un campo con questo nome.", "danger", "admin_config")
    field.name = name
    field.field_type = field_type
    field.options = options
    field.unit = unit
    field.sort_order = sort_order
    field.is_active = is_active
    db.session.commit()
    flash("Campo personalizzato aggiornato.", "success")
    return redirect(url_for("admin_config"))

@app.route("/admin/custom_fields/<int:field_id>/delete", methods=["POST"])
@login_required
def delete_custom_field(field_id):
    field = CustomField.query.get_or_404(field_id)
    ItemCustomFieldValue.query.filter_by(field_id=field.id).delete()
    CategoryFieldSetting.query.filter_by(field_key=custom_field_key(field.id)).delete()
    db.session.delete(field)
    db.session.commit()
    flash("Campo personalizzato eliminato.", "success")
    return redirect(url_for("admin_config"))

@app.route("/admin/settings/update", methods=["POST"])
@login_required
def update_settings():
    s = get_settings()
    try:
        s.label_w_mm  = float(request.form.get("label_w_mm"))
        s.label_h_mm  = float(request.form.get("label_h_mm"))
        s.margin_tb_mm= float(request.form.get("margin_tb_mm"))
        s.margin_lr_mm= float(request.form.get("margin_lr_mm"))
        s.gap_mm      = float(request.form.get("gap_mm"))
        s.label_padding_mm = float(request.form.get("label_padding_mm"))
        s.label_qr_size_mm = float(request.form.get("label_qr_size_mm"))
        s.label_qr_margin_mm = float(request.form.get("label_qr_margin_mm"))
        s.label_position_width_mm = float(request.form.get("label_position_width_mm"))
        s.label_position_font_pt = float(request.form.get("label_position_font_pt"))
        s.label_page_format = normalize_page_format(request.form.get("label_page_format"), DEFAULT_LABEL_PAGE_FORMAT)
        s.dymo_label_w_mm = float(request.form.get("dymo_label_w_mm"))
        s.dymo_label_h_mm = float(request.form.get("dymo_label_h_mm"))
        s.dymo_margin_x_mm = float(request.form.get("dymo_margin_x_mm"))
        s.dymo_margin_y_mm = float(request.form.get("dymo_margin_y_mm"))
        s.dymo_font_name = (request.form.get("dymo_font_name") or DEFAULT_DYMO_FONT_NAME).strip() or DEFAULT_DYMO_FONT_NAME
        s.dymo_font_size_pt = float(request.form.get("dymo_font_size_pt"))
        s.dymo_show_category = bool(request.form.get("dymo_show_category"))
        s.dymo_show_subtype = bool(request.form.get("dymo_show_subtype"))
        s.dymo_show_thread = bool(request.form.get("dymo_show_thread"))
        s.dymo_show_measure = bool(request.form.get("dymo_show_measure"))
        s.dymo_show_main = bool(request.form.get("dymo_show_main"))
        s.dymo_show_material = bool(request.form.get("dymo_show_material"))
        s.dymo_show_position = bool(request.form.get("dymo_show_position"))
        s.card_w_mm = float(request.form.get("card_w_mm"))
        s.card_h_mm = float(request.form.get("card_h_mm"))
        s.card_margin_tb_mm = float(request.form.get("card_margin_tb_mm"))
        s.card_margin_lr_mm = float(request.form.get("card_margin_lr_mm"))
        s.card_gap_mm = float(request.form.get("card_gap_mm"))
        s.card_padding_mm = float(request.form.get("card_padding_mm"))
        s.card_qr_size_mm = float(request.form.get("card_qr_size_mm"))
        s.card_qr_margin_mm = float(request.form.get("card_qr_margin_mm"))
        s.card_position_width_mm = float(request.form.get("card_position_width_mm"))
        s.card_position_font_pt = float(request.form.get("card_position_font_pt"))
        s.card_gap_h_mm = s.card_gap_mm
        s.card_gap_v_mm = s.card_gap_mm
        s.card_page_format = normalize_page_format(request.form.get("card_page_format"), DEFAULT_CARD_PAGE_FORMAT)
        s.orientation_landscape = bool(request.form.get("orientation_landscape"))
        s.card_orientation_landscape = bool(request.form.get("card_orientation_landscape"))
        s.qr_default  = bool(request.form.get("qr_default"))
        url = request.form.get("qr_base_url","").strip()
        s.qr_base_url = url or None
        db.session.commit()
        flash("Impostazioni aggiornate.", "success")
    except Exception as e:
        db.session.rollback(); flash(f"Errore salvataggio: {e}", "danger")
    return redirect(url_for("admin_config"))

@app.route("/admin/mqtt/update", methods=["POST"])
@login_required
def update_mqtt_settings():
    s = get_mqtt_settings()
    try:
        s.enabled = bool(request.form.get("enabled"))
        s.host = (request.form.get("host") or "").strip() or None
        s.port = int(request.form.get("port") or DEFAULT_MQTT_PORT)
        s.username = (request.form.get("username") or "").strip() or None
        password = request.form.get("password") or ""
        if password:
            s.password = password
        if request.form.get("clear_password"):
            s.password = None
        s.topic = (request.form.get("topic") or "").strip() or None
        s.qos = int(request.form.get("qos") or DEFAULT_MQTT_QOS)
        s.retain = bool(request.form.get("retain"))
        s.client_id = (request.form.get("client_id") or "").strip() or None
        s.include_cabinet_name = bool(request.form.get("include_cabinet_name"))
        s.include_cabinet_id = bool(request.form.get("include_cabinet_id"))
        s.include_location_name = bool(request.form.get("include_location_name"))
        s.include_location_id = bool(request.form.get("include_location_id"))
        s.include_row = bool(request.form.get("include_row"))
        s.include_col = bool(request.form.get("include_col"))
        s.include_slot_label = bool(request.form.get("include_slot_label"))
        s.include_items = bool(request.form.get("include_items"))
        s.include_item_id = bool(request.form.get("include_item_id"))
        s.include_item_name = bool(request.form.get("include_item_name"))
        s.include_item_category = bool(request.form.get("include_item_category"))
        s.include_item_category_color = bool(request.form.get("include_item_category_color"))
        s.include_item_quantity = bool(request.form.get("include_item_quantity"))
        s.include_item_position = bool(request.form.get("include_item_position"))
        s.include_item_description = bool(request.form.get("include_item_description"))
        s.include_item_material = bool(request.form.get("include_item_material"))
        s.include_item_finish = bool(request.form.get("include_item_finish"))
        s.include_empty = bool(request.form.get("include_empty"))
        db.session.commit()
        flash("Configurazione MQTT aggiornata.", "success")
    except Exception as e:
        db.session.rollback()
        flash(f"Errore salvataggio MQTT: {e}", "danger")
    return redirect(url_for("admin_config"))

@app.route("/admin/locations/add", methods=["POST"])
@login_required
def add_location():
    name = request.form.get("name","").strip()
    if len(name) < 2:
        return _flash_back("Nome ubicazione troppo corto.", "danger", "admin_config")
    if Location.query.filter_by(name=name).first():
        return _flash_back("Ubicazione già esistente.", "danger", "admin_config")
    db.session.add(Location(name=name)); db.session.commit()
    flash("Ubicazione aggiunta.", "success"); return redirect(url_for("admin_config"))

@app.route("/admin/locations/<int:loc_id>/update", methods=["POST"])
@login_required
def update_location(loc_id):
    loc = Location.query.get_or_404(loc_id)
    name = request.form.get("name","").strip()
    if len(name) < 2:
        return _flash_back("Nome ubicazione troppo corto.", "danger", "admin_config")
    if Location.query.filter(Location.id!=loc.id, Location.name==name).first():
        return _flash_back("Esiste già un’ubicazione con questo nome.", "danger", "admin_config")
    loc.name=name; db.session.commit()
    flash("Ubicazione aggiornata.", "success"); return redirect(url_for("admin_config"))

@app.route("/admin/locations/<int:loc_id>/delete", methods=["POST"])
@login_required
def delete_location(loc_id):
    loc = Location.query.get_or_404(loc_id)
    has_cab = Cabinet.query.filter_by(location_id=loc.id).first()
    if has_cab:
        flash("Impossibile eliminare: ci sono cassettiere collegate.", "danger")
    else:
        db.session.delete(loc); db.session.commit(); flash("Ubicazione eliminata.", "success")
    return redirect(url_for("admin_config"))

@app.route("/admin/cabinets/add", methods=["POST"])
@login_required
def add_cabinet():
    try: location_id = int(request.form.get("location_id"))
    except: return _flash_back("Seleziona ubicazione valida.", "danger", "admin_config")
    name = request.form.get("name","").strip()
    rows = int(request.form.get("rows_max") or 128)
    cols = request.form.get("cols_max","ZZ").strip().upper()
    comps= int(request.form.get("compartments_per_slot") or 6)
    if len(name) < 2:
        return _flash_back("Nome cassettiera troppo corto.", "danger", "admin_config")
    if Cabinet.query.filter_by(name=name).first():
        return _flash_back("Nome cassettiera già in uso.", "danger", "admin_config")
    db.session.add(Cabinet(location_id=location_id, name=name, rows_max=rows, cols_max=cols, compartments_per_slot=comps))
    db.session.commit(); flash("Cassettiera aggiunta.", "success"); return redirect(url_for("admin_config"))

@app.route("/admin/cabinets/<int:cab_id>/update", methods=["POST"])
@login_required
def update_cabinet(cab_id):
    cab = Cabinet.query.get_or_404(cab_id)
    name  = request.form.get("name","").strip()
    rows  = int(request.form.get("rows_max") or cab.rows_max)
    cols  = request.form.get("cols_max","ZZ").strip().upper()
    comps = int(request.form.get("compartments_per_slot") or cab.compartments_per_slot)
    if len(name) < 2:
        return _flash_back("Nome cassettiera troppo corto.", "danger", "admin_config")
    if Cabinet.query.filter(Cabinet.id!=cab.id, Cabinet.name==name).first():
        return _flash_back("Nome cassettiera già in uso.", "danger", "admin_config")
    cab.name=name; cab.rows_max=rows; cab.cols_max=cols; cab.compartments_per_slot=comps
    db.session.commit(); flash("Cassettiera aggiornata.", "success"); return redirect(url_for("admin_config"))

@app.route("/admin/cabinets/<int:cab_id>/delete", methods=["POST"])
@login_required
def delete_cabinet(cab_id):
    cab = Cabinet.query.get_or_404(cab_id)
    has_slots = Slot.query.filter_by(cabinet_id=cab.id).first()
    if has_slots:
        flash("Impossibile eliminare: la cassettiera ha slot assegnati.", "danger")
    else:
        db.session.delete(cab); db.session.commit(); flash("Cassettiera eliminata.", "success")
    return redirect(url_for("admin_config"))

@app.route("/admin/cabinets/merge_add", methods=["POST"])
@login_required
def add_drawer_merge():
    try:
        cab_id = int(request.form.get("cabinet_id"))
    except Exception:
        return _flash_back("Cassettiera non valida.", "danger", "admin_config")
    cab = Cabinet.query.get_or_404(cab_id)
    col_start = (request.form.get("col_start") or "").strip().upper()
    col_end = (request.form.get("col_end") or "").strip().upper()
    try:
        row_start = int(request.form.get("row_start"))
        row_end = int(request.form.get("row_end"))
        row_start, row_end, col_start, col_end = normalize_merge_bounds(
            cab, col_start, col_end, row_start, row_end
        )
    except Exception as exc:
        return _flash_back(str(exc), "danger", "admin_config")

    new_start_idx = colcode_to_idx(col_start)
    new_end_idx = colcode_to_idx(col_end)
    existing = DrawerMerge.query.filter_by(cabinet_id=cab.id).all()
    for m in existing:
        m_start_idx = colcode_to_idx(m.col_start)
        m_end_idx = colcode_to_idx(m.col_end)
        rows_overlap = not (row_end < m.row_start or row_start > m.row_end)
        cols_overlap = not (new_end_idx < m_start_idx or new_start_idx > m_end_idx)
        if rows_overlap and cols_overlap:
            return _flash_back("La fusione si sovrappone a un'altra già definita.", "danger", "admin_config")

    db.session.add(DrawerMerge(
        cabinet_id=cab.id,
        row_start=row_start,
        row_end=row_end,
        col_start=col_start,
        col_end=col_end,
    ))
    db.session.commit()
    flash("Fusione cassetti aggiunta.", "success")
    return redirect(url_for("admin_config"))

@app.route("/admin/cabinets/merge/<int:merge_id>/delete", methods=["POST"])
@login_required
def delete_drawer_merge(merge_id):
    merge = DrawerMerge.query.get_or_404(merge_id)
    db.session.delete(merge)
    db.session.commit()
    flash("Fusione cassetti eliminata.", "success")
    return redirect(url_for("admin_config"))

def _ensure_slot(cab_id:int, col_code:str, row_num:int) -> Slot:
    s = Slot.query.filter_by(cabinet_id=cab_id, col_code=col_code.upper(), row_num=row_num).first()
    if not s:
        s = Slot(cabinet_id=cab_id, col_code=col_code.upper(), row_num=row_num, is_blocked=False)
        db.session.add(s); db.session.flush()
    return s

def _slot_categories(slot_id:int) -> set:
    rows = (
        db.session.query(Item.category_id)
        .join(Assignment, Assignment.item_id == Item.id)
        .filter(Assignment.slot_id == slot_id)
        .distinct()
        .all()
    )
    return {cat_id for (cat_id,) in rows if cat_id}

def _slot_capacity_ok(cabinet:Cabinet, assigns_count:int, col_code:str, row_num:int) -> bool:
    max_comp = _max_compartments_for_slot(cabinet, col_code, row_num)
    return assigns_count <= max_comp

def _reassign_compartments(slot_id:int, cabinet:Cabinet):
    assigns = Assignment.query.filter_by(slot_id=slot_id).order_by(Assignment.id).all()
    slot = db.session.get(Slot, slot_id)
    max_comp = _max_compartments_for_slot(cabinet, slot.col_code, slot.row_num)
    n = 1
    for a in assigns:
        if n>max_comp: raise RuntimeError("Capienza scomparti superata.")
        a.compartment_no = n; n += 1

def _move_slot_assignments(src_slot: Slot, dst_slot: Slot, dst_cabinet: Cabinet, *, move_labels: bool = False):
    src_assigns = Assignment.query.filter_by(slot_id=src_slot.id).all()
    for a in src_assigns:
        a.slot_id = dst_slot.id

    if move_labels:
        dst_slot.display_label_override = src_slot.display_label_override
        dst_slot.print_label_override = src_slot.print_label_override
        src_slot.display_label_override = None
        src_slot.print_label_override = None

    _reassign_compartments(dst_slot.id, dst_cabinet)

@app.route("/admin/slots/block", methods=["POST"])
@login_required
def block_slot():
    cab_id = int(request.form.get("cabinet_id"))
    col    = request.form.get("col_code","").upper().strip()
    row    = int(request.form.get("row_num"))
    if not column_code_valid(col) or not (1<=row<=128):
        return _flash_back("Colonna/riga non validi.", "danger", "admin_config")
    region = merge_region_for(cab_id, col, row)
    cells = merge_cells_from_region(region) if region else [(col, row)]
    slots = [_ensure_slot(cab_id, c, r) for c, r in cells]
    if any(Assignment.query.filter_by(slot_id=slot.id).first() for slot in slots):
        flash("Impossibile bloccare: cassetto occupato.", "danger")
    else:
        for slot in slots:
            slot.is_blocked = True
        db.session.commit()
        flash("Cella bloccata.", "success")
    return redirect(url_for("admin_config"))

@app.route("/admin/slots/unblock", methods=["POST"])
@login_required
def unblock_slot():
    cab_id = int(request.form.get("cabinet_id"))
    col    = request.form.get("col_code","").upper().strip()
    row    = int(request.form.get("row_num"))
    if not column_code_valid(col) or not (1<=row<=128):
        return _flash_back("Colonna/riga non validi.", "danger", "admin_config")
    region = merge_region_for(cab_id, col, row)
    cells = merge_cells_from_region(region) if region else [(col, row)]
    for c, r in cells:
        slot = _ensure_slot(cab_id, c, r)
        slot.is_blocked = False
    db.session.commit()
    flash("Cella sbloccata.", "success")
    return redirect(url_for("admin_config"))

@app.route("/admin/slots/move", methods=["POST"])
@login_required
def move_slot():
    try:
        cab_from = int(request.form.get("cabinet_from"))
        col_from = request.form.get("col_from","").upper().strip()
        row_from = int(request.form.get("row_from"))
        cab_to   = int(request.form.get("cabinet_to"))
        col_to   = request.form.get("col_to","").upper().strip()
        row_to   = int(request.form.get("row_to"))
        do_swap  = bool(request.form.get("swap"))
    except Exception:
        return _flash_back("Parametri non validi.", "danger", "admin_config")
    if not (column_code_valid(col_from) and column_code_valid(col_to) and 1<=row_from<=128 and 1<=row_to<=128):
        return _flash_back("Colonna/riga non validi.", "danger", "admin_config")

    region_from = merge_region_for(cab_from, col_from, row_from)
    if region_from:
        col_from = region_from["anchor_col"]
        row_from = region_from["anchor_row"]
    region_to = merge_region_for(cab_to, col_to, row_to)
    if region_to:
        col_to = region_to["anchor_col"]
        row_to = region_to["anchor_row"]

    src = Slot.query.filter_by(cabinet_id=cab_from, col_code=col_from, row_num=row_from).first()
    if not src: return _flash_back("Slot origine inesistente.", "danger", "admin_config")
    dst = _ensure_slot(cab_to, col_to, row_to)
    if dst.is_blocked: return _flash_back("Destinazione bloccata.", "danger", "admin_config")
    if src.is_blocked: return _flash_back("Origine bloccata.", "danger", "admin_config")

    src_assigns = Assignment.query.filter_by(slot_id=src.id).all()
    dst_assigns = Assignment.query.filter_by(slot_id=dst.id).all()
    if not src_assigns:
        flash("Nessun contenuto nel cassetto origine.", "warning"); return redirect(url_for("admin_config"))

    src_cats = _slot_categories(src.id)
    dst_cats = _slot_categories(dst.id)
    if dst_assigns and (src_cats and dst_cats) and (list(src_cats)[0] != list(dst_cats)[0]):
        return _flash_back("Le categorie dei cassetti non coincidono.", "danger", "admin_config")

    cab_to_obj = db.session.get(Cabinet, cab_to)
    cab_from_obj = db.session.get(Cabinet, cab_from)

    if not do_swap:
        if not _slot_capacity_ok(cab_to_obj, len(dst_assigns)+len(src_assigns), dst.col_code, dst.row_num):
            return _flash_back("Scomparti insufficienti nel cassetto destinazione.", "danger", "admin_config")
        _move_slot_assignments(src, dst, cab_to_obj, move_labels=True)
        db.session.commit(); flash("Cassetto spostato.", "success")
    else:
        if (
            not _slot_capacity_ok(cab_to_obj, len(dst_assigns)+len(src_assigns), dst.col_code, dst.row_num)
            or not _slot_capacity_ok(cab_from_obj, len(src_assigns)+len(dst_assigns), src.col_code, src.row_num)
        ):
            return _flash_back("Scomparti insufficienti per lo scambio.", "danger", "admin_config")
        for a in src_assigns: a.slot_id = dst.id
        for a in dst_assigns: a.slot_id = src.id
        _reassign_compartments(dst.id, cab_to_obj)
        _reassign_compartments(src.id, cab_from_obj)
        db.session.commit(); flash("Cassetti scambiati.", "success")
    return redirect(url_for("admin_config"))

# ===================== CLICK-TO-ASSIGN API =====================
@app.route("/admin/unplaced.json")
@login_required
def api_unplaced():
    cat_id = request.args.get("category_id", type=int)
    subq = select(Assignment.item_id)
    q = Item.query.filter(Item.id.not_in(subq))
    if cat_id: q = q.filter(Item.category_id == cat_id)
    items = q.order_by(Item.category_id, Item.id).all()
    return jsonify([{"id":it.id,"caption":auto_name_for(it),"category_id":it.category_id} for it in items])

@app.route("/admin/grid_assign", methods=["POST"])
@login_required
def grid_assign():
    try:
        item_id  = int(request.form.get("item_id"))
        cabinet_id = int(request.form.get("cabinet_id"))
        col_code = request.form.get("col_code","").upper().strip()
        row_num  = int(request.form.get("row_num"))
    except Exception:
        return jsonify({"ok":False, "error":"Parametri non validi."}), 400
    item = Item.query.get(item_id)
    if not item: return jsonify({"ok":False, "error":"Articolo inesistente."}), 404
    force_share = bool(request.form.get("force_share"))
    try:
        _assign_position(item, cabinet_id, col_code, row_num, force_share=force_share)
        db.session.commit()
    except SharePermissionError as e:
        db.session.rollback()
        blockers = [{"id": it.id, "name": auto_name_for(it)} for it in e.items]
        return jsonify({"ok":False, "error":str(e), "share_blockers": blockers}), 409
    except Exception as e:
        db.session.rollback()
        return jsonify({"ok":False, "error":str(e)}), 400
    return jsonify({"ok":True})

@app.route("/admin/slot_items")
@login_required
def slot_items():
    cab_id = request.args.get("cabinet_id", type=int)
    col_code = (request.args.get("col_code") or "").strip().upper()
    row_num = request.args.get("row_num", type=int)
    if not (cab_id and col_code and row_num):
        return jsonify({"ok": False, "error": "Parametri mancanti."}), 400

    region = merge_region_for(cab_id, col_code, row_num)
    if region:
        col_code = region["anchor_col"]
        row_num = region["anchor_row"]
        cells = merge_cells_from_region(region)
    else:
        cells = [(col_code, row_num)]

    slots = (
        Slot.query.filter(Slot.cabinet_id == cab_id)
        .filter(or_(*[
            (Slot.col_code == col) & (Slot.row_num == row)
            for col, row in cells
        ]))
        .all()
    )
    if not slots:
        return jsonify({"ok": True, "items": []})

    default_label = f"{col_code}{row_num}"
    anchor_slot = next((s for s in slots if s.col_code == col_code and s.row_num == row_num), slots[0])
    label_display = slot_label(anchor_slot, for_display=True, fallback_col=col_code, fallback_row=row_num)
    label_print = slot_label(anchor_slot, for_display=False, fallback_col=col_code, fallback_row=row_num)

    slot_ids = [s.id for s in slots]
    assigns = (
        db.session.query(Assignment, Item, Category, Slot)
        .join(Item, Assignment.item_id == Item.id)
        .join(Category, Item.category_id == Category.id, isouter=True)
        .join(Slot, Assignment.slot_id == Slot.id)
        .filter(Assignment.slot_id.in_(slot_ids))
        .order_by(Slot.col_code, Slot.row_num, Assignment.compartment_no)
        .all()
    )

    items = []
    for a, it, cat, slot in assigns:
        items.append({
            "id": it.id,
            "name": auto_name_for(it),
            "quantity": it.quantity,
            "category": cat.name if cat else None,
            "color": cat.color if cat else "#999999",
            "position": slot_label(slot, for_display=True, fallback_col=slot.col_code, fallback_row=slot.row_num),
            "position_code": f"{slot.col_code}{slot.row_num}",
            "main_measure": main_measure_info(it),
        })
    return jsonify({
        "ok": True,
        "items": items,
        "slot_label_display": label_display,
        "slot_label_print": label_print,
        "default_label": default_label,
    })

@app.route("/admin/slot_label", methods=["GET", "POST"])
@login_required
def slot_label_endpoint():
    cab_id = request.values.get("cabinet_id", type=int)
    col_code = (request.values.get("col_code") or "").strip().upper()
    row_num = request.values.get("row_num", type=int)
    if not (cab_id and col_code and row_num):
        return jsonify({"ok": False, "error": "Parametri mancanti."}), 400
    cabinet = Cabinet.query.get(cab_id)
    if not cabinet:
        return jsonify({"ok": False, "error": "Cassettiera non trovata."}), 404
    region = merge_region_for(cabinet.id, col_code, row_num)
    if region:
        col_code = region["anchor_col"]
        row_num = region["anchor_row"]
    try:
        slot = _ensure_slot(cabinet.id, col_code, int(row_num))
    except Exception as e:
        db.session.rollback()
        return jsonify({"ok": False, "error": str(e)}), 400

    if request.method == "POST":
        display_label = (request.form.get("display_label") or "").strip()
        print_label = (request.form.get("print_label") or "").strip()
        slot.display_label_override = display_label or None
        slot.print_label_override = print_label or None
        db.session.commit()

    default_label = f"{slot.col_code}{slot.row_num}"
    return jsonify({
        "ok": True,
        "display_label": slot.display_label_override,
        "print_label": slot.print_label_override,
        "default_label": default_label,
        "effective_display_label": slot_label(slot, for_display=True, fallback_col=slot.col_code, fallback_row=slot.row_num),
        "effective_print_label": slot_label(slot, for_display=False, fallback_col=slot.col_code, fallback_row=slot.row_num),
        "cabinet_name": cabinet.name,
    })

@app.route("/admin/mqtt/publish_slot", methods=["POST"])
@login_required
def mqtt_publish_slot():
    payload = request.get_json(silent=True) or {}
    cab_id = payload.get("cabinet_id")
    col_code = (payload.get("col_code") or "").strip().upper()
    row_num = payload.get("row_num")
    try:
        cab_id = int(cab_id)
        row_num = int(row_num)
    except Exception:
        return jsonify({"ok": False, "error": "Parametri non validi."}), 400
    if not col_code:
        return jsonify({"ok": False, "error": "Colonna non valida."}), 400
    cabinet = Cabinet.query.get(cab_id)
    if not cabinet:
        return jsonify({"ok": False, "error": "Cassettiera non trovata."}), 404
    settings = get_mqtt_settings()
    mqtt_payload = mqtt_payload_for_slot(cabinet, col_code, row_num, settings)
    if mqtt_payload is None:
        return jsonify({"ok": False, "skipped": True, "error": "Nessun contenuto da pubblicare."}), 200
    result = publish_mqtt_payload(mqtt_payload, settings)
    status = 200 if result.get("ok") else 500
    if result.get("skipped"):
        status = 200
    return jsonify(result), status


# ===================== KATODO.COM — PRESTASHOP INTEGRATION =====================

@app.route("/admin/katodo/settings", methods=["GET", "POST"])
@login_required
def katodo_settings():
    s = get_katodo_settings()
    if request.method == "POST":
        try:
            s.enabled = bool(request.form.get("enabled"))
            url = (request.form.get("api_url") or "").strip()
            s.api_url = url or "https://katodo.com/api/"
            if request.form.get("clear_api_key"):
                s.api_key = None
            else:
                key = (request.form.get("api_key") or "").strip()
                if key:
                    s.api_key = key
            db.session.commit()
            flash("Configurazione Katodo salvata.", "success")
        except Exception as e:
            db.session.rollback()
            flash(f"Errore salvataggio: {e}", "danger")
        return redirect(url_for("katodo_settings"))
    return render_template("admin/katodo_settings.html", s=s)

@app.route("/admin/katodo/test", methods=["POST"])
@login_required
def katodo_test():
    s = get_katodo_settings()
    result = prestashop_api_request("", s, timeout=8)
    if result["ok"]:
        data = result["data"] or []
        resources = data if isinstance(data, list) else list((data.get("api", data)).keys())
        return jsonify({"ok": True, "resources": resources})
    return jsonify({"ok": False, "error": result["error"], "status_code": result["status_code"]})

@app.route("/admin/katodo/field_discovery")
@login_required
def katodo_field_discovery():
    s = get_katodo_settings()
    schema_result = prestashop_api_request("products", s, params={"schema": "full"})
    example_result = None
    example_id = None

    list_result = prestashop_api_request("products", s)
    if list_result["ok"]:
        ids = (list_result["data"] or {}).get("products", [])
        if ids:
            first = ids[0]
            example_id = first.get("id") if isinstance(first, dict) else first
            if example_id:
                example_result = prestashop_api_request(f"products/{example_id}", s)

    schema_fields = {}
    example_values = {}

    if schema_result["ok"]:
        raw = schema_result["data"] or {}
        product_schema = raw.get("product", {})
        for key, meta in product_schema.items():
            if isinstance(meta, dict):
                attrs = meta.get("@attributes", {})
                schema_fields[key] = {
                    "type": attrs.get("type", ""),
                    "required": attrs.get("required", ""),
                }
            else:
                schema_fields[key] = {"type": type(meta).__name__, "required": ""}

    if example_result and example_result["ok"]:
        product_data = (example_result["data"] or {}).get("product", {})
        for key, val in product_data.items():
            if isinstance(val, dict):
                lang_vals = val.get("language", [])
                if isinstance(lang_vals, list) and lang_vals:
                    first_lang = lang_vals[0]
                    example_values[key] = str(first_lang.get("#text", first_lang))[:120]
                elif isinstance(lang_vals, dict):
                    example_values[key] = str(lang_vals.get("#text", ""))[:120]
                else:
                    example_values[key] = str(val)[:120]
            else:
                example_values[key] = str(val)[:120] if val is not None else ""

    return render_template(
        "admin/katodo_field_discovery.html",
        s=s,
        schema_fields=schema_fields,
        example_values=example_values,
        example_id=example_id,
        schema_error=schema_result.get("error"),
        example_error=example_result.get("error") if example_result else None,
    )

@app.route("/admin/katodo/products")
@login_required
def katodo_products():
    s = get_katodo_settings()
    products = KatodoProduct.query.order_by(KatodoProduct.reference).all()
    last_sync = db.session.query(db.func.max(KatodoProduct.synced_at)).scalar()
    return render_template("admin/katodo_products.html", s=s, products=products,
                           last_sync=last_sync, ps_image_url=ps_image_url)

@app.route("/admin/katodo/import", methods=["POST"])
@login_required
def katodo_import():
    s = get_katodo_settings()

    def _sse(data: dict) -> str:
        import json as _json
        return f"data: {_json.dumps(data)}\n\n"

    def _flt(val):
        try:
            return float(val) if val not in (None, "", "0.000000") else None
        except (ValueError, TypeError):
            return None

    def generate():
        import json as _json

        if not s.enabled or not s.api_key:
            yield _sse({"done": True, "error": "Integrazione non configurata."})
            return

        # ---- categorie ----
        app.logger.info("[Katodo import] Caricamento categorie...")
        yield _sse({"step": "Caricamento categorie…", "progress": 2, "done": False})
        cats_result = prestashop_api_request("categories", s,
                                             params={"display": "[id,name]", "language": "1"},
                                             timeout=60)
        if not cats_result["ok"]:
            msg = f"Errore categorie: {cats_result['error']}"
            app.logger.error(f"[Katodo import] {msg}")
            yield _sse({"done": True, "error": msg})
            return
        category_cache = {str(c["id"]): c.get("name", "")
                          for c in cats_result["data"].get("categories", cats_result["data"])}
        app.logger.info(f"[Katodo import] {len(category_cache)} categorie caricate.")
        yield _sse({"step": f"{len(category_cache)} categorie caricate.", "progress": 5, "done": False})

        # ---- paginazione prodotti ----
        display_fields = "[id,reference,supplier_reference,manufacturer_name,id_category_default,price,wholesale_price,weight,active,date_add,date_upd,id_default_image,name,description_short,description,quantity]"
        page_size = 25      # piccolo per server lenti — aggiorna UI ogni 25 prodotti
        offset = 0
        total_new = 0
        total_upd = 0
        now = datetime.now(timezone.utc).replace(tzinfo=None)

        while True:
            limit = f"{page_size},{offset}" if offset else str(page_size)
            app.logger.info(f"[Katodo import] Richiesta prodotti offset={offset} limit={page_size}…")
            yield _sse({"step": f"Recupero prodotti {offset + 1}–{offset + page_size}…",
                        "progress": min(10 + offset // 6, 90), "done": False})

            result = prestashop_api_request("products", s,
                                            params={"display": display_fields, "language": "1", "limit": limit},
                                            timeout=120)
            if not result["ok"]:
                msg = f"Errore prodotti (offset {offset}): {result['error']}"
                app.logger.error(f"[Katodo import] {msg}")
                yield _sse({"done": True, "error": msg})
                return

            page_prods = result["data"].get("products", result["data"]) if isinstance(result["data"], dict) else result["data"]
            if not page_prods:
                app.logger.info("[Katodo import] Nessun altro prodotto — fine paginazione.")
                break

            for p in page_prods:
                ps_id = int(p.get("id", 0) or 0)
                if not ps_id:
                    continue

                date_add = date_upd = None
                try:
                    raw_add = str(p.get("date_add") or "")
                    if raw_add and raw_add.replace("0","").replace("-","").replace(" ","").replace(":",""):
                        date_add = datetime.strptime(raw_add, "%Y-%m-%d %H:%M:%S")
                    raw_upd = str(p.get("date_upd") or "")
                    if raw_upd and raw_upd.replace("0","").replace("-","").replace(" ","").replace(":",""):
                        date_upd = datetime.strptime(raw_upd, "%Y-%m-%d %H:%M:%S")
                except (ValueError, TypeError):
                    pass

                ps_image_id = None
                try:
                    v = int(p.get("id_default_image") or 0)
                    if v > 0:
                        ps_image_id = v
                except (TypeError, ValueError):
                    pass

                fields = dict(
                    reference          = p.get("reference") or None,
                    supplier_reference = p.get("supplier_reference") or None,
                    name               = p.get("name") or None,
                    description_short  = p.get("description_short") or None,
                    description        = p.get("description") or None,
                    manufacturer_name  = p.get("manufacturer_name") or None,
                    category_name      = category_cache.get(str(p.get("id_category_default", ""))),
                    price              = _flt(p.get("price")),
                    wholesale_price    = _flt(p.get("wholesale_price")),
                    weight             = _flt(p.get("weight")),
                    active             = str(p.get("active")) == "1",
                    quantity           = int(p.get("quantity") or 0),
                    ps_image_id        = ps_image_id,
                    ps_date_add        = date_add,
                    ps_date_upd        = date_upd,
                    synced_at          = now,
                )
                existing = KatodoProduct.query.filter_by(ps_id=ps_id).first()
                if existing:
                    for k, v in fields.items():
                        setattr(existing, k, v)
                    total_upd += 1
                else:
                    db.session.add(KatodoProduct(ps_id=ps_id, **fields))
                    total_new += 1

            db.session.commit()
            processed = offset + len(page_prods)
            app.logger.info(f"[Katodo import] Salvati {processed} prodotti (nuovi={total_new} aggiornati={total_upd}).")
            yield _sse({"step": f"Salvati {processed} prodotti (nuovi: {total_new}, agg.: {total_upd})",
                        "progress": min(10 + processed // 6, 90), "done": False,
                        "count": processed})
            offset += len(page_prods)
            if len(page_prods) < page_size:
                break

        app.logger.info(f"[Katodo import] Completato — nuovi={total_new} aggiornati={total_upd} totale={total_new+total_upd}")
        yield _sse({"done": True, "new": total_new, "updated": total_upd,
                    "total": total_new + total_upd, "progress": 100,
                    "step": "Importazione completata!"})

    return Response(
        stream_with_context(generate()),
        content_type="text/event-stream",
        headers={"X-Accel-Buffering": "no", "Cache-Control": "no-cache"},
    )

@app.route("/admin/katodo/products/<int:ps_id>", methods=["GET", "POST"])
@login_required
def katodo_product_detail(ps_id):
    s = get_katodo_settings()
    p = KatodoProduct.query.filter_by(ps_id=ps_id).first_or_404()
    if request.method == "POST":
        try:
            p.reference          = (request.form.get("reference") or "").strip() or None
            p.supplier_reference = (request.form.get("supplier_reference") or "").strip() or None
            p.name               = (request.form.get("name") or "").strip() or None
            p.description_short  = request.form.get("description_short") or None
            p.description        = request.form.get("description") or None
            p.manufacturer_name  = (request.form.get("manufacturer_name") or "").strip() or None
            p.category_name      = (request.form.get("category_name") or "").strip() or None
            price_raw = request.form.get("price", "").strip()
            p.price = float(price_raw) if price_raw else None
            wp_raw = request.form.get("wholesale_price", "").strip()
            p.wholesale_price = float(wp_raw) if wp_raw else None
            w_raw = request.form.get("weight", "").strip()
            p.weight = float(w_raw) if w_raw else None
            p.active   = bool(request.form.get("active"))
            qty_raw = request.form.get("quantity", "0").strip()
            p.quantity = int(qty_raw) if qty_raw.lstrip("-").isdigit() else p.quantity
            db.session.commit()
            flash("Prodotto aggiornato.", "success")
        except Exception as e:
            db.session.rollback()
            flash(f"Errore: {e}", "danger")
        return redirect(url_for("katodo_product_detail", ps_id=ps_id))
    return render_template("admin/katodo_product_detail.html", s=s, p=p, ps_image_url=ps_image_url)


@app.route("/admin/slot_items/<int:item_id>/clear", methods=["POST"])
@login_required
def slot_clear_item(item_id):
    slot_ids = [a.slot_id for a in Assignment.query.filter_by(item_id=item_id).all()]
    Assignment.query.filter_by(item_id=item_id).delete()
    if slot_ids:
        remaining = {
            sid for (sid,) in db.session.query(Assignment.slot_id)
            .filter(Assignment.slot_id.in_(slot_ids))
            .distinct()
            .all()
        }
        empty_slots = [sid for sid in set(slot_ids) if sid not in remaining]
        if empty_slots:
            Slot.query.filter(Slot.id.in_(empty_slots)).update(
                {
                    Slot.display_label_override: None,
                    Slot.print_label_override: None,
                },
                synchronize_session=False,
            )
    db.session.commit()
    return jsonify({"ok": True})

# ===================== ASSEGNAMENTO AUTOMATICO =====================
def _iter_cabinet_walk(cabinet: Cabinet, start_col: str, start_row: int, direction: str):
    """
    Generatore di celle a partire da (start_col, start_row) nella cassettiera indicata.
    direction = "H" (orizzontale) o "V" (verticale).
    """
    if not cabinet:
        raise ValueError("Cassettiera inesistente.")
    cols = list(iter_cols_upto(cabinet.cols_max or "Z"))
    rows = list(range(1, min(128, max(1, int(cabinet.rows_max))) + 1))

    start_col = (start_col or "").strip().upper()
    if start_col not in cols:
        raise ValueError("Colonna di partenza fuori dalla cassettiera selezionata.")
    try:
        row_num_int = int(start_row)
    except Exception:
        raise ValueError("Riga di partenza non valida.")
    if row_num_int not in rows:
        raise ValueError("Riga di partenza fuori dalla cassettiera selezionata.")

    col_index0 = cols.index(start_col)
    row_index0 = rows.index(row_num_int)
    direction = (direction or "H").upper()

    if direction == "V":
        # dall'alto verso il basso, poi colonna successiva
        for ci in range(col_index0, len(cols)):
            for ri in range(row_index0 if ci == col_index0 else 0, len(rows)):
                yield cols[ci], rows[ri]
    else:
        # da sinistra a destra, poi riga successiva
        for ri in range(row_index0, len(rows)):
            for ci in range(col_index0 if ri == row_index0 else 0, len(cols)):
                yield cols[ci], rows[ri]


def _thread_size_sort_columns():
    normalized = func.trim(Item.thread_size)
    size_order = (
        select(ThreadSize.sort_order)
        .join(ThreadStandard, ThreadSize.standard_id == ThreadStandard.id)
        .where(ThreadStandard.code == Item.thread_standard, ThreadSize.value == normalized)
        .scalar_subquery()
    )
    numeric_part = case((
        normalized.ilike("M%"),
        func.cast(func.replace(func.substr(normalized, 2), ",", "."), db.Float),
    ))
    size_rank = func.coalesce(size_order, numeric_part)
    return [size_rank, normalized, Item.thread_size]


def _sort_columns_for_key(key: str):
    sort_map = {
        "id": [Item.id],
        "thread_size": _thread_size_sort_columns(),
        "subtype": [Subtype.name],
        "thickness_mm": [Item.thickness_mm],
        "length_mm": [Item.length_mm],
        "outer_d_mm": [Item.outer_d_mm],
        "material": [Material.name],
    }
    return sort_map.get(key, [])


def _auto_assign_category(category_id: int,
                          cabinet_id: int,
                          start_col: str,
                          start_row: int,
                          direction: str,
                          primary_key: str,
                          secondary_key: str,
                          tertiary_key: str,
                          quaternary_key: str,
                          count: int,
                          clear_occupied: bool):
    """
    Esegue l'assegnamento automatico di `count` articoli (non ancora posizionati)
    della categoria indicata, a partire dalla cella indicata nella cassettiera scelta.
    Ritorna un dict con qualche statistica sull'operazione.
    """
    if count <= 0:
        raise ValueError("Il numero di articoli da posizionare deve essere maggiore di zero.")

    cab = db.session.get(Cabinet, int(cabinet_id))
    if not cab:
        raise ValueError("Cassettiera inesistente.")

    # Articoli non ancora posizionati per la categoria
    subq = select(Assignment.item_id)
    q = Item.query.filter(Item.id.not_in(subq), Item.category_id == int(category_id))

    order_cols = []
    sort_keys = [primary_key, secondary_key, tertiary_key, quaternary_key]
    sort_keys = [k for k in sort_keys if k]

    if "subtype" in sort_keys:
        q = q.outerjoin(Subtype, Item.subtype_id == Subtype.id)
    if "material" in sort_keys:
        q = q.outerjoin(Material, Item.material_id == Material.id)

    used = set()
    for key in sort_keys:
        if key in used:
            continue
        used.add(key)
        order_cols.extend(_sort_columns_for_key(key))
    if not order_cols:
        order_cols = [Item.id]
    q = q.order_by(*order_cols)

    all_candidates = q.all()
    if not all_candidates:
        raise ValueError("Nessun articolo non posizionato per la categoria selezionata.")
    items = all_candidates[:count]
    requested = len(items)
    total_unplaced = len(all_candidates)

    assignments_plan = []   # (item, col_code, row_num)
    skipped_occupied = set()   # celle saltate perché già occupate (clear_occupied=False)
    reused_slots = set()       # celle che verranno liberate e riutilizzate (clear_occupied=True)
    planned_items = {}         # key -> lista di Item (esistenti + pianificati) per compatibilità
    slot_plan = []             # lista ordinata di slot percorsi con capacità residua e contenuto

    for col_code, row_num in _iter_cabinet_walk(cab, start_col, start_row, direction):
        slot = Slot.query.filter_by(cabinet_id=cab.id, col_code=col_code, row_num=row_num).first()
        if slot and slot.is_blocked:
            continue
        slot_key = (col_code, row_num)
        assigns = []
        slot_items = []
        if slot:
            assigns, slot_items = _load_slot_assignments(slot.id)
        has_content = bool(assigns)
        if has_content and clear_occupied:
            reused_slots.add(slot_key)
            slot_items = []
            existing_count = 0
        else:
            existing_count = len(assigns)

        max_here = _max_compartments_for_slot(cab, col_code, row_num)
        free_here = max_here - existing_count
        if free_here <= 0:
            if has_content and not clear_occupied:
                skipped_occupied.add(slot_key)
            continue

        planned_items.setdefault(slot_key, slot_items.copy())
        slot_plan.append({
            "key": slot_key,
            "col": col_code,
            "row": row_num,
            "has_content": has_content,
            "remaining": free_here,
        })

    if not slot_plan:
        raise ValueError("Nessuna cella disponibile per l'assegnamento automatico.")

    for itm in items:
        placed = False
        # 1) preferisce riutilizzare cassetti già occupati e compatibili
        for info in slot_plan:
            if not info["has_content"]:
                continue
            if info["remaining"] <= 0:
                continue
            if not _can_share_slot(planned_items[info["key"]], itm):
                skipped_occupied.add(info["key"])
                continue
            assignments_plan.append((itm, info["col"], info["row"]))
            planned_items[info["key"]].append(itm)
            info["remaining"] -= 1
            placed = True
            break

        if placed:
            continue

        # 2) altrimenti usa celle vuote (o liberate)
        for info in slot_plan:
            if info["remaining"] <= 0:
                continue
            if not _can_share_slot(planned_items[info["key"]], itm):
                if info["has_content"] and not clear_occupied:
                    skipped_occupied.add(info["key"])
                continue
            assignments_plan.append((itm, info["col"], info["row"]))
            planned_items[info["key"]].append(itm)
            info["remaining"] -= 1
            placed = True
            break

        if not placed:
            break

    if not assignments_plan:
        if skipped_occupied and not clear_occupied:
            raise ValueError("Tutte le celle nel percorso sono già popolate o bloccate; nessun articolo assegnato.")
        raise ValueError("Nessuna cella disponibile per l'assegnamento automatico.")

    cleared_slots = 0
    assigned = 0
    try:
        if clear_occupied and reused_slots:
            for col_code, row_num in sorted(reused_slots):
                slot = Slot.query.filter_by(cabinet_id=cab.id, col_code=col_code, row_num=row_num).first()
                if slot:
                    deleted = Assignment.query.filter_by(slot_id=slot.id).delete()
                    if deleted:
                        cleared_slots += 1

        for item, col_code, row_num in assignments_plan:
            _assign_position(item, cab.id, col_code, row_num)
            assigned += 1
        touched_cells = {(col_code, row_num) for _, col_code, row_num in assignments_plan}
        for col_code, row_num in touched_cells:
            anchor_slot, _, _, slot_items = _collect_region_assignments(cab.id, col_code, row_num)
            auto_label = shared_drawer_label(slot_items)
            if not auto_label:
                continue
            if not (anchor_slot.display_label_override or "").strip():
                anchor_slot.display_label_override = auto_label
            if not (anchor_slot.print_label_override or "").strip():
                anchor_slot.print_label_override = auto_label
        db.session.commit()
    except Exception:
        db.session.rollback()
        raise

    collisions_count = len(reused_slots) if clear_occupied else len(set(skipped_occupied))
    return {
        "assigned": assigned,
        "cleared_slots": cleared_slots,
        "collisions": collisions_count,
        "requested": requested,
        "total_unplaced": total_unplaced,
    }


def _deallocate_category_from_cabinet(
    category_id: int,
    cabinet_id: int,
    start_col: str | None = None,
    start_row: int | None = None,
    direction: str | None = None,
    cells_count: int | None = None,
):
    cab = db.session.get(Cabinet, int(cabinet_id))
    if not cab:
        raise ValueError("Cassettiera inesistente.")

    cat = db.session.get(Category, int(category_id))
    if not cat:
        raise ValueError("Categoria inesistente.")

    slot_ids = None
    scope = "all"
    if start_col and start_row and cells_count and cells_count > 0:
        scope = "range"
        walk = _iter_cabinet_walk(cab, start_col, start_row, (direction or "H").upper())
        coords = list(islice(walk, int(cells_count)))
        if not coords:
            raise ValueError("Nessuna cella valida nell'intervallo indicato.")
        slot_map = {
            (s.col_code, s.row_num): s.id
            for s in Slot.query.filter_by(cabinet_id=cab.id).all()
        }
        slot_ids = [slot_map[(c, r)] for c, r in coords if (c, r) in slot_map]
        if not slot_ids:
            raise ValueError("Nessuna cella trovata nell'intervallo indicato.")

    assigns_query = (
        db.session.query(Assignment.id, Assignment.slot_id)
        .join(Item, Assignment.item_id == Item.id)
        .join(Slot, Assignment.slot_id == Slot.id)
        .filter(Item.category_id == int(category_id), Slot.cabinet_id == int(cabinet_id))
    )
    if slot_ids is not None:
        assigns_query = assigns_query.filter(Assignment.slot_id.in_(slot_ids))
    assigns = assigns_query.all()

    if not assigns:
        return {
            "removed": 0,
            "slots": 0,
            "cabinet": cab.name,
            "category": cat.name,
            "scope": scope,
        }

    assign_ids = [a.id for a in assigns]
    slot_ids = {a.slot_id for a in assigns}

    deleted = Assignment.query.filter(Assignment.id.in_(assign_ids)).delete(synchronize_session=False)
    remaining_slots = {
        sid for (sid,) in db.session.query(Assignment.slot_id)
        .filter(Assignment.slot_id.in_(slot_ids))
        .distinct()
        .all()
    }
    empty_slots = [sid for sid in slot_ids if sid not in remaining_slots]
    if empty_slots:
        Slot.query.filter(Slot.id.in_(empty_slots)).update(
            {
                Slot.display_label_override: None,
                Slot.print_label_override: None,
            },
            synchronize_session=False,
        )
    db.session.commit()

    return {
        "removed": deleted,
        "slots": len(slot_ids),
        "cabinet": cab.name,
        "category": cat.name,
        "scope": scope,
    }


def _placements_internal(target_endpoint="cassettiere"):
    cabinets = Cabinet.query.order_by(Cabinet.name).all()
    categories = Category.query.order_by(Category.name).all()
    sort_options = [
        ("thread_size",  "Misura"),
        ("subtype", "Sottotipo (forma)"),
        ("length_mm", "Lunghezza/Spessore (mm)"),
        ("outer_d_mm", "Ø esterno (mm)"),
        ("material",     "Materiale"),
        ("id",           "ID articolo"),
    ]

    # Valori di default letti dalla querystring
    form_cabinet_id  = request.args.get("cabinet_id", type=int)
    form_category_id = request.args.get("category_id", type=int)
    primary_key      = request.args.get("primary_key") or "thread_size"
    secondary_key    = request.args.get("secondary_key") or "subtype"
    tertiary_key     = request.args.get("tertiary_key") or "length_mm"
    quaternary_key   = request.args.get("quaternary_key") or "material"
    direction        = (request.args.get("direction") or "H").upper()
    count_val        = request.args.get("count", type=int) or 10
    start_col        = (request.args.get("start_col") or "").strip().upper()
    start_row        = request.args.get("start_row", type=int)
    clear_occupied   = bool(request.args.get("clear_occupied", type=int))

    if not form_cabinet_id and cabinets:
        form_cabinet_id = cabinets[0].id

    if request.method == "POST":
        form = request.form
        action = form.get("action") or "auto_assign"
        try:
            form_cabinet_id  = int(form.get("cabinet_id") or 0)
            form_category_id = int(form.get("category_id") or 0)
        except Exception:
            flash("Parametri non validi per l'assegnamento automatico.", "danger")
            return redirect(url_for(target_endpoint))

        primary_key    = form.get("primary_key") or primary_key or "thread_size"
        secondary_key  = form.get("secondary_key") or secondary_key or "subtype"
        tertiary_key   = form.get("tertiary_key") or tertiary_key or "length_mm"
        quaternary_key = form.get("quaternary_key") or quaternary_key or "material"
        direction      = (form.get("direction") or direction or "H").upper()
        count_raw = form.get("count")
        count_val = int(count_raw) if count_raw not in (None, "") else (count_val or 0)
        start_col      = (form.get("start_col") or start_col or "").strip().upper()
        start_row_raw  = form.get("start_row")
        start_row      = int(start_row_raw) if (start_row_raw not in (None, "")) else start_row
        clear_occupied = bool(form.get("clear_occupied"))
        clear_scope    = (form.get("clear_scope") or "all").lower()
        if action != "clear_category" or clear_scope == "range":
            count_val = max(1, int(count_val or 1))

        if action == "clear_category":
            if not (form_cabinet_id and form_category_id):
                flash("Seleziona cassettiera e categoria da de-allocare.", "danger")
            else:
                try:
                    range_params = {}
                    if clear_scope == "range":
                        if not (start_col and start_row):
                            raise ValueError("Per de-allocare un intervallo seleziona colonna e riga di partenza.")
                        if count_val <= 0:
                            raise ValueError("Numero di celle da de-allocare non valido.")
                        range_params = {
                            "start_col": start_col,
                            "start_row": start_row,
                            "direction": direction,
                            "cells_count": count_val,
                        }
                    res = _deallocate_category_from_cabinet(
                        form_category_id,
                        form_cabinet_id,
                        **range_params,
                    )
                    removed = res["removed"]
                    slots = res["slots"]
                    cat_name = res.get("category")
                    cab_name = res.get("cabinet")
                    scope = res.get("scope") or "all"
                    if removed:
                        msg = (
                            f"De-allocati {removed} articoli della categoria \"{cat_name}\" "
                            f"dalla cassettiera \"{cab_name}\"."
                        )
                        if slots:
                            msg += f" Cassetti liberati: {slots}."
                        if scope == "range":
                            msg += " Intervallo: sono state considerate solo le celle indicate."
                        msg += " Dovrai ristampare le etichette e riposizionare i cassetti."
                        flash(msg, "warning")
                    else:
                        flash("Nessun articolo di questa categoria è assegnato nella cassettiera selezionata.", "info")
                except ValueError as e:
                    flash(str(e), "danger")
                except Exception as e:
                    db.session.rollback()
                    flash(f"Errore durante la de-allocazione: {e}", "danger")

            return redirect(url_for(
                target_endpoint,
                cabinet_id=form_cabinet_id or "",
                category_id=form_category_id or "",
                primary_key=primary_key,
                secondary_key=secondary_key,
                tertiary_key=tertiary_key,
                quaternary_key=quaternary_key,
                direction=direction,
                count=count_val,
                start_col=start_col,
                start_row=start_row or "",
                clear_occupied=int(clear_occupied),
            ))

        if not (form_cabinet_id and form_category_id and start_col and start_row):
            flash("Seleziona cassettiera, categoria e cella di partenza.", "danger")
            return redirect(url_for(
                target_endpoint,
                cabinet_id=form_cabinet_id or "",
                category_id=form_category_id or "",
                primary_key=primary_key,
                secondary_key=secondary_key,
                tertiary_key=tertiary_key,
                quaternary_key=quaternary_key,
                direction=direction,
                count=count_val,
                start_col=start_col,
                start_row=start_row,
                clear_occupied=int(clear_occupied),
            ))

        try:
            res = _auto_assign_category(
                category_id=form_category_id,
                cabinet_id=form_cabinet_id,
                start_col=start_col,
                start_row=start_row,
                direction=direction,
                primary_key=primary_key,
                secondary_key=secondary_key,
                tertiary_key=tertiary_key,
                quaternary_key=quaternary_key,
                count=count_val,
                clear_occupied=clear_occupied,
            )
            assigned       = res["assigned"]
            cleared_slots  = res["cleared_slots"]
            collisions     = res["collisions"]
            requested      = res["requested"]
            total_unplaced = res["total_unplaced"]

            if assigned == 0:
                flash("Nessun articolo assegnato: controlla i parametri o la cella di partenza.", "warning")
            else:
                msg = f"Assegnati {assigned} articoli."
                if requested > assigned:
                    msg += f" Solo {assigned} articoli su {requested} richiesti hanno trovato una cella disponibile."
                if cleared_slots:
                    msg += f" De-allocate {cleared_slots} celle precedentemente popolate."
                elif collisions and not clear_occupied:
                    msg += f" {collisions} celle nel percorso erano già popolate e non sono state modificate."
                msg += f" Articoli non posizionati rimanenti per la categoria: {total_unplaced - assigned}."
                flash(msg, "success")
        except ValueError as e:
            flash(str(e), "danger")
        except Exception as e:
            flash(f"Errore nell'assegnamento automatico: {e}", "danger")

        return redirect(url_for(
            target_endpoint,
            cabinet_id=form_cabinet_id,
            category_id=form_category_id,
            primary_key=primary_key,
            secondary_key=secondary_key,
            tertiary_key=tertiary_key,
            quaternary_key=quaternary_key,
            direction=direction,
            count=count_val,
            start_col=start_col,
            start_row=start_row,
            clear_occupied=int(clear_occupied),
        ))

    # GET o dopo redirect: preparo i dati per il template
    grid = build_full_grid(form_cabinet_id) if form_cabinet_id else {"rows": [], "cols": [], "cells": {}, "cab": None}

    subq = select(Assignment.item_id)
    unplaced_by_category = dict(
        db.session.query(Item.category_id, func.count(Item.id))
        .filter(Item.id.not_in(subq))
        .group_by(Item.category_id)
        .all()
    )
    unplaced_count = None
    if form_category_id:
        unplaced_count = unplaced_by_category.get(form_category_id, 0)
    items_to_place = Item.query.filter(Item.id.not_in(subq)).all()

    can_manage_placements = current_user.is_authenticated and current_user.has_permission("manage_placements")
    can_manage_items = current_user.is_authenticated and current_user.has_permission("manage_items")
    unplaced_json = [
        {"id": it.id, "caption": auto_name_for(it), "category_id": it.category_id}
        for it in items_to_place
    ] if can_manage_placements else []

    return render_template(
        "cassettiere.html",
        categories=categories,
        cabinets=cabinets,
        selected_cab_id=form_cabinet_id,
        grid=grid,
        unplaced_json=unplaced_json,
        can_manage_placements=can_manage_placements,
        can_manage_items=can_manage_items,
        sort_options=sort_options,
        form_cabinet_id=form_cabinet_id,
        form_category_id=form_category_id,
        primary_key=primary_key,
        secondary_key=secondary_key,
        tertiary_key=tertiary_key,
        quaternary_key=quaternary_key,
        direction=direction,
        count=count_val,
        start_col=start_col,
        start_row=start_row,
        clear_occupied=clear_occupied,
        unplaced_count=unplaced_count,
        unplaced_by_category=unplaced_by_category,
        items_to_place=items_to_place,
    )

@app.route("/admin/posizionamento", methods=["GET", "POST"])
@login_required
def placements():
    if request.method == "GET":
        return redirect(url_for("cassettiere", **request.args))
    return _placements_internal("cassettiere")

@app.route("/admin/auto_assign", methods=["GET", "POST"])
@login_required
def auto_assign():
    if request.method == "GET":
        return redirect(url_for("cassettiere", **request.args))
    return _placements_internal("cassettiere")


# ===================== ETICHETTE PDF =====================
def wrap_to_lines(text: str, font_name: str, font_size: float, max_width_pt: float, max_lines: int = 2):
    from reportlab.pdfbase import pdfmetrics

    if not text:
        return []
    words = text.split()
    lines = []
    cur = ""
    for w in words:
        test = (cur + " " + w).strip()
        if pdfmetrics.stringWidth(test, font_name, font_size) <= max_width_pt:
            cur = test
        else:
            if cur:
                lines.append(cur)
                if len(lines) == max_lines:
                    return lines
                cur = w
            else:
                for i in range(len(w), 0, -1):
                    piece = w[:i] + "…"
                    if pdfmetrics.stringWidth(piece, font_name, font_size) <= max_width_pt:
                        lines.append(piece)
                        cur = ""
                        break
                if len(lines) == max_lines:
                    return lines
    if cur and len(lines) < max_lines:
        lines.append(cur)
    return lines


@app.route("/admin/labels/pdf", methods=["POST"])
@login_required
def labels_pdf():
    try:
        from reportlab.pdfgen import canvas
        from reportlab.lib.pagesizes import landscape, portrait
        from reportlab.graphics.shapes import Drawing
        from reportlab.graphics import renderPDF
        from reportlab.lib.colors import HexColor
        from reportlab.graphics.barcode import qr as qrmod
        from reportlab.pdfbase import pdfmetrics
    except Exception:
        flash("Per la stampa etichette installa reportlab: pip install reportlab", "danger")
        return redirect(request.referrer or url_for("admin_items"))

    slot_ids = [int(x) for x in request.form.getlist("slot_ids") if str(x).isdigit()]
    ids = request.form.getlist("item_ids")
    if slot_ids:
        ids = [
            row[0]
            for row in db.session.query(Assignment.item_id)
            .filter(Assignment.slot_id.in_(slot_ids))
            .all()
        ]
    if not ids:
        ids = [row[0] for row in db.session.query(Item.id).all()]
    items = Item.query.filter(Item.id.in_(ids)).order_by(Item.id).all()
    if not items:
        flash("Nessun articolo valido per la stampa.", "warning"); return redirect(request.referrer or url_for("admin_items"))

    assignments = (db.session.query(Assignment.item_id, Cabinet, Slot)
                   .join(Slot, Assignment.slot_id == Slot.id)
                   .join(Cabinet, Slot.cabinet_id == Cabinet.id)
                   .filter(Assignment.item_id.in_(ids))
                   .all())
    pos_by_item = {item_id: (cab, slot) for item_id, cab, slot in assignments}
    original_order = {item.id: idx for idx, item in enumerate(items)}

    slot_ids = {slot.id for _, slot in pos_by_item.values() if slot and slot.id}
    slot_contents = {}
    if slot_ids:
        rows = (
            db.session.query(Item, Slot, Cabinet)
            .join(Assignment, Assignment.item_id == Item.id)
            .join(Slot, Assignment.slot_id == Slot.id)
            .join(Cabinet, Slot.cabinet_id == Cabinet.id)
            .filter(Assignment.slot_id.in_(slot_ids))
            .all()
        )
        for it, slot, cab in rows:
            key = slot.id
            slot_contents.setdefault(key, []).append(it)

    def _label_sort_key(entry):
        items_in_entry = entry.get("items", [])
        cab, slot = entry.get("position") or (None, None)
        base_order = min((original_order.get(it.id, 0) for it in items_in_entry), default=0)
        if cab and slot:
            col_code = getattr(slot, "col_code", "") or ""
            row_num = getattr(slot, "row_num", 0) or 0
            return (0, cab.name or "", int(row_num), colcode_to_idx(col_code), base_order)
        return (1, base_order)

    def _common_parts(items_list: list[Item]) -> list[str]:
        if not items_list:
            return []
        parts = []
        cats = {it.category.name for it in items_list if it.category}
        if len(cats) == 1:
            parts.append(next(iter(cats)))
        subtypes = {it.subtype.name for it in items_list if it.subtype}
        if len(subtypes) == 1:
            parts.append(next(iter(subtypes)))
        thread_sizes = {it.thread_size for it in items_list if it.thread_size}
        if len(thread_sizes) == 1:
            parts.append(next(iter(thread_sizes)))
        def _main_value(it: Item):
            if is_screw(it) or is_standoff(it) or is_spacer(it):
                return getattr(it, "length_mm", None)
            return getattr(it, "outer_d_mm", None)
        main_values = {format_mm_short(_main_value(it)) for it in items_list if _main_value(it) is not None}
        if len(main_values) == 1:
            mv = next(iter(main_values))
            if mv is not None:
                tag = "L" if any(is_screw(it) or is_standoff(it) or is_spacer(it) for it in items_list) else "Øe"
                parts.append(f"{tag}{mv}")
        materials = {it.material.name for it in items_list if it.material}
        if len(materials) == 1:
            parts.append(next(iter(materials)))
        return parts

    s = get_settings()
    include_qr = s.qr_default

    buf = io.BytesIO()
    base_page_size = page_size_for_format(s.label_page_format)
    page_size = (landscape(base_page_size) if s.orientation_landscape else portrait(base_page_size))
    c = canvas.Canvas(buf, pagesize=page_size)
    page_w, page_h = page_size

    margin_x = mm_to_pt(s.margin_lr_mm)
    margin_y = mm_to_pt(s.margin_tb_mm)
    lab_w = mm_to_pt(s.label_w_mm)
    lab_h = mm_to_pt(s.label_h_mm)
    gap   = mm_to_pt(s.gap_mm)

    cols = int((page_w - 2*margin_x + gap) // (lab_w + gap))
    rows = int((page_h - 2*margin_y + gap) // (lab_h + gap))
    if cols < 1 or rows < 1:
        label_format_name = page_format_label(s.label_page_format)
        flash(f"Configurazione etichette non valida rispetto al formato {label_format_name}.", "danger")
        return redirect(request.referrer or url_for("admin_items"))

    x0 = margin_x
    y0 = page_h - margin_y - lab_h

    def crop_marks(cx, cy, w, h):
        mark = mm_to_pt(1.2)
        c.setStrokeColorRGB(0, 0, 0); c.setLineWidth(0.2)
        c.line(cx,        cy+h, cx+mark, cy+h); c.line(cx+w-mark, cy+h, cx+w,    cy+h)
        c.line(cx,        cy,   cx+mark, cy);   c.line(cx+w-mark, cy,   cx+w,    cy)
        c.line(cx,        cy+h, cx,      cy+h-mark); c.line(cx,  cy,   cx,      cy+mark)
        c.line(cx+w,      cy+h, cx+w,    cy+h-mark); c.line(cx+w,cy,   cx+w,    cy+mark)

    title_font = "Helvetica-Bold"
    title_size = 7.2
    cat_font = "Helvetica-Bold"
    cat_size = 7.4

    padding_x = mm_to_pt(getattr(s, "label_padding_mm", DEFAULT_LABEL_PADDING_MM) or DEFAULT_LABEL_PADDING_MM)
    qr_box = mm_to_pt(getattr(s, "label_qr_size_mm", DEFAULT_LABEL_QR_SIZE_MM) or DEFAULT_LABEL_QR_SIZE_MM) if include_qr else 0
    qr_margin = mm_to_pt(getattr(s, "label_qr_margin_mm", DEFAULT_LABEL_QR_MARGIN_MM) or DEFAULT_LABEL_QR_MARGIN_MM) if qr_box else 0
    qr_area_width = qr_box + (qr_margin * 2 if qr_box else 0)
    base_pos_block_w = mm_to_pt(getattr(s, "label_position_width_mm", DEFAULT_LABEL_POSITION_WIDTH_MM) or DEFAULT_LABEL_POSITION_WIDTH_MM)
    position_font_size = getattr(s, "label_position_font_pt", DEFAULT_LABEL_POSITION_FONT_PT) or DEFAULT_LABEL_POSITION_FONT_PT
    position_line_height = position_font_size + 0.6

    def _type_text(item: Item) -> str:
        # Base: name o descrizione auto-generata, senza la categoria duplicata
        base = item.name or auto_name_for(item)
        cat_name = item.category.name if item.category else ""
        if cat_name and base.lower().startswith(cat_name.lower() + " "):
            base = base[len(cat_name) + 1 :].lstrip()

        # Layout dedicato per le rondelle: tipo + Øi + Øe + spessore
        if is_washer(item):
            parts = []

            # Subtipo, senza ripetere "Rondelle/Rondella"
            if getattr(item, "subtype", None) and item.subtype.name:
                st = item.subtype.name
                lower_st = st.lower()
                if lower_st.startswith("rondell"):
                    # elimina la parola iniziale "Rondelle"/"Rondella"
                    st = st.split(" ", 1)[-1]
                parts.append(st)

            if item.thread_size:
                parts.append(item.thread_size)

            if item.inner_d_mm:
                v = format_mm_short(item.inner_d_mm)
                if v is not None:
                    parts.append(f"Øi{v}")

            if item.outer_d_mm:
                v = format_mm_short(item.outer_d_mm)
                if v is not None:
                    parts.append(f"Øe{v}")

            v = format_mm_short(unified_thickness_value(item))
            if v is not None:
                prefix = THICKNESS_ABBR if item.thickness_mm is not None else LENGTH_ABBR
                parts.append(f"{prefix} {v}")

            if parts:
                return " ".join(parts)

        # Per gli altri oggetti: se c'è spessore, aggiungi un breve "sX"
        v = format_mm_short(unified_thickness_value(item))
        if v is not None:
            prefix = THICKNESS_ABBR if item.thickness_mm is not None else LENGTH_ABBR
            formatted = f"{prefix} {v}"
            if formatted not in base:
                base = f"{base} {formatted}"

        return base

    def _single_line(text: str, font_name: str, font_size: float, max_width_pt: float) -> str:
        """Restituisce una singola riga che entra nella larghezza disponibile."""
        if not text:
            return ""
        lines = wrap_to_lines(text, font_name, font_size, max_width_pt, max_lines=1)
        return lines[0] if lines else ""

    label_entries = []
    seen_slot_keys = set()
    for item in items:
        pos_data = pos_by_item.get(item.id)
        if pos_data:
            cab, slot = pos_data
            slot_key = slot.id if slot else None
            if slot_key and slot_key in seen_slot_keys:
                continue
            if slot_key:
                seen_slot_keys.add(slot_key)
            slot_items = slot_contents.get(slot_key, [item])
            slot_items.sort(key=lambda it: original_order.get(it.id, 10**6))
            label_entries.append({
                "items": slot_items,
                "position": (cab, slot),
                "slot_id": slot_key,
                "is_multi": len(slot_items) > 1,
                "has_print_override": bool(slot and (slot.print_label_override or "").strip()),
                "color": slot_items[0].category.color if slot_items and slot_items[0].category else "#000000",
            })
        else:
            label_entries.append({
                "items": [item],
                "position": (None, None),
                "slot_id": None,
                "is_multi": False,
                "has_print_override": False,
                "color": item.category.color if item.category else "#000000",
            })
    for entry in label_entries:
        if entry["is_multi"]:
            summary_parts = _common_parts(entry["items"])
            summary = " ".join(summary_parts).strip()
            entry["summary"] = f"{summary} - MULTY" if summary else "MULTY"
        else:
            entry["summary"] = None
    label_entries.sort(key=_label_sort_key)

    for idx, entry in enumerate(label_entries):
        items_in_entry = entry["items"]
        if not items_in_entry:
            continue
        item = items_in_entry[0]
        col = idx % cols
        row = (idx // cols) % rows
        if idx > 0 and idx % (cols * rows) == 0:
            c.showPage()

        x = x0 + col * (lab_w + gap)
        y = y0 - row * (lab_h + gap)

        crop_marks(x, y, lab_w, lab_h)
        try:
            colhex = entry.get("color") or "#000000"
            bg_inset = mm_to_pt(0.5)
            bg_w = max(lab_w - (bg_inset * 2), 0)
            bg_h = max(lab_h - (bg_inset * 2), 0)
            if bg_w > 0 and bg_h > 0:
                c.setFillColor(HexColor(colhex))
                c.rect(x + bg_inset, y + bg_inset, bg_w, bg_h, stroke=0, fill=1)
        except Exception:
            pass
        c.setStrokeColorRGB(0, 0, 0)
        c.setLineWidth(0.3)
        c.rect(x, y, lab_w, lab_h, stroke=1, fill=0)

        pos_data = entry.get("position") or (None, None)
        cab, slot = pos_data

        # Se il cassetto è condiviso o ha una label di stampa personalizzata,
        # stampo il nome cassetto come etichetta principale (stile cassetto multi-articolo).
        if entry.get("is_multi") or entry.get("has_print_override"):
            col_code = getattr(slot, "col_code", "") or ""
            row_num = getattr(slot, "row_num", None)
            label_txt = slot_label(slot, for_display=False, fallback_col=col_code, fallback_row=row_num) or ""
            row_col_lines = []
            if row_num is not None and col_code:
                row_col_lines = [f"Rig: {int(row_num)}", f"Col: {col_code.upper()}"]

            # Posizione (solo righe/colonne) su blocco a destra
            pos_texts = row_col_lines or []
            pos_font_size = position_font_size
            pos_line_height = pos_font_size + 0.6
            pos_block_w = base_pos_block_w if pos_texts else 0
            if pos_texts:
                required_w = max(pdfmetrics.stringWidth(txt, "Helvetica-Bold", pos_font_size) for txt in pos_texts) + mm_to_pt(1)
                pos_block_w = max(pos_block_w, required_w)
            pos_x = x + lab_w - pos_block_w - (padding_x if pos_block_w else 0)

            # Testo centrale (Stampa etichette) adattato a due righe
            text_area_w = lab_w - pos_block_w - (padding_x * 2 if pos_block_w else padding_x * 2)
            text_left = x + padding_x
            text_top_available = lab_h - padding_x * 2
            font_name = "Helvetica-Bold"
            font_size = min(12.0, (text_top_available / 2) - 0.2)
            font_size = max(font_size, 6.0)
            line_spacing = font_size + 0.6
            lines = wrap_to_lines(label_txt, font_name, font_size, text_area_w, max_lines=2) or [label_txt]
            while ((len(lines) * line_spacing) > text_top_available or any(pdfmetrics.stringWidth(l, font_name, font_size) > text_area_w for l in lines)) and font_size > 6.0:
                font_size = max(font_size - 0.5, 6.0)
                line_spacing = font_size + 0.6
                lines = wrap_to_lines(label_txt, font_name, font_size, text_area_w, max_lines=2) or [label_txt]
            total_height = (len(lines) - 1) * line_spacing + font_size
            start_y = y + (lab_h / 2) + (total_height / 2) - font_size

            c.setFillColorRGB(0, 0, 0)
            c.setFont(font_name, font_size)
            line_y = start_y
            for ln in lines:
                c.drawString(text_left, line_y, ln)
                line_y -= line_spacing

            if pos_texts:
                c.setFont("Helvetica-Bold", pos_font_size)
                block_height = pos_line_height * len(pos_texts)
                pos_start_y = y + (lab_h / 2) + (block_height / 2) - pos_font_size
                line_y = pos_start_y
                for txt in pos_texts:
                    c.drawString(pos_x, line_y, txt)
                    line_y -= pos_line_height
            continue

        c.setFillColorRGB(0, 0, 0)

        pos_texts = None
        pos_block_w = base_pos_block_w
        pos_font_size = position_font_size
        pos_line_height = position_line_height
        custom_slot_label = False
        if cab or slot:
            col_code = getattr(slot, "col_code", "") or ""
            row_num = getattr(slot, "row_num", None)
            label_txt = slot_label(slot, for_display=False, fallback_col=col_code, fallback_row=row_num)
            row_col_lines = []
            if row_num is not None and col_code:
                row_col_lines = [f"Rig: {int(row_num)}", f"Col: {col_code.upper()}"]
            if slot and slot.print_label_override:
                custom_slot_label = True
                pos_font_size = max(position_font_size - 1.0, 4.0)
                available_w = max(pos_block_w - mm_to_pt(1), mm_to_pt(6))
                pos_texts = wrap_to_lines(label_txt, "Helvetica-Bold", pos_font_size, available_w, max_lines=2) or [label_txt]
                pos_line_height = pos_font_size + 0.6
                combined_lines = list(pos_texts) + row_col_lines
                available_h = qr_box if qr_box else lab_h - padding_x
                while combined_lines and (pos_line_height * len(combined_lines)) > available_h and pos_font_size > 4.0:
                    pos_font_size = max(pos_font_size - 0.4, 4.0)
                    pos_line_height = pos_font_size + 0.6
                    pos_texts = wrap_to_lines(label_txt, "Helvetica-Bold", pos_font_size, available_w, max_lines=2) or [label_txt]
                    combined_lines = list(pos_texts) + row_col_lines
                pos_texts = combined_lines or row_col_lines
                if pos_texts:
                    max_width = max(pdfmetrics.stringWidth(txt, "Helvetica-Bold", pos_font_size) for txt in pos_texts)
                    pos_block_w = max(pos_block_w, max_width + mm_to_pt(1))
            elif row_col_lines:
                pos_texts = row_col_lines
                required_w = max(pdfmetrics.stringWidth(txt, "Helvetica-Bold", pos_font_size) for txt in pos_texts) + mm_to_pt(1)
                pos_block_w = max(pos_block_w, required_w)

        # area testuale a sinistra del blocco posizione/QR
        text_right_limit = lab_w - qr_area_width - pos_block_w - padding_x
        text_right_limit = max(text_right_limit, mm_to_pt(10))
        text_x = x + padding_x

        c.setFillColorRGB(0, 0, 0)

        # punto di partenza dall'alto
        cy = y + lab_h - max(padding_x, mm_to_pt(1.0))

        # --- Riga 1: Categoria + Sottotipo + Misura ---
        base_lines = label_lines_for_item(item)
        line1_text = base_lines[0] if base_lines else ""
        if line1_text:
            line1_lines = wrap_to_lines(line1_text, cat_font, cat_size, text_right_limit, max_lines=1)
            if line1_lines:
                c.setFont(cat_font, cat_size)
                c.drawString(text_x, cy - cat_size, line1_lines[0])
                cy -= (cat_size + 0.6)

        # --- Riga 2: specifiche a seconda della categoria ---
        line2_text = base_lines[1] if len(base_lines) > 1 else ""
        if line2_text:
            line2_lines = wrap_to_lines(line2_text, title_font, title_size, text_right_limit, max_lines=1)
            if line2_lines:
                c.setFont(title_font, title_size)
                c.drawString(text_x, cy - title_size, line2_lines[0])
                cy -= (title_size + 0.6)

        # Fallback: se per qualche motivo non abbiamo scritto nulla, uso il nome completo
        if not line1_text and not line2_text:
            fallback = item.name or auto_name_for(item)
            lines = wrap_to_lines(fallback, title_font, title_size, text_right_limit, max_lines=2)
            c.setFont(title_font, title_size)
            for ln in lines:
                c.drawString(text_x, cy - title_size, ln)
                cy -= (title_size + 0.6)

        # posizione a sinistra del QR, su due righe
        if pos_texts:
            pos_x = x + lab_w - qr_area_width - pos_block_w
            if qr_box:
                block_height = pos_line_height * len(pos_texts)
                start_y = y + qr_margin + max((qr_box - block_height) / 2, 0) + block_height - pos_font_size
            else:
                start_y = y + lab_h - padding_x - pos_font_size
            if custom_slot_label:
                start_y -= mm_to_pt(0.5)
            c.setFont("Helvetica-Bold", pos_font_size)
            line_y = start_y
            for txt in pos_texts:
                c.drawString(pos_x, line_y, txt)
                line_y -= pos_line_height

        # QR a destra
        if qr_box:
            try:
                s = get_settings()
                if s.qr_base_url:
                    url = f"{s.qr_base_url.rstrip('/')}/api/items/{item.id}.json"
                else:
                    url = f"{request.host_url.rstrip('/')}/api/items/{item.id}.json"
                qr_code = qrmod.QrCodeWidget(url)
                bounds = qr_code.getBounds()
                w = bounds[2] - bounds[0]
                h = bounds[3] - bounds[1]
                scale = min(qr_box / w, qr_box / h)
                d = Drawing(w, h)
                d.add(qr_code)
                c.saveState()
                c.translate(x + lab_w - qr_box - qr_margin, y + qr_margin)
                c.scale(scale, scale)
                renderPDF.draw(d, c, 0, 0)
                c.restoreState()
            except Exception:
                pass
    c.save(); buf.seek(0)
    return send_file(buf, as_attachment=True, download_name="etichette.pdf", mimetype="application/pdf")

@app.route("/admin/dymo/pdf", methods=["POST"])
@login_required
def dymo_labels_pdf():
    try:
        from reportlab.pdfgen import canvas
        from reportlab.pdfbase import pdfmetrics
    except Exception:
        flash("Per la stampa etichette DYMO installa reportlab: pip install reportlab", "danger")
        return redirect(request.referrer or url_for("admin_items"))

    slot_ids = [int(x) for x in request.form.getlist("slot_ids") if str(x).isdigit()]
    ids = request.form.getlist("item_ids")
    if slot_ids:
        ids = [
            row[0]
            for row in db.session.query(Assignment.item_id)
            .filter(Assignment.slot_id.in_(slot_ids))
            .all()
        ]
    if not ids:
        ids = [row[0] for row in db.session.query(Item.id).all()]
    items = Item.query.filter(Item.id.in_(ids)).order_by(Item.id).all()
    if not items:
        flash("Nessun articolo valido per la stampa.", "warning")
        return redirect(request.referrer or url_for("admin_items"))

    assignments = (db.session.query(Assignment.item_id, Cabinet, Slot)
                   .join(Slot, Assignment.slot_id == Slot.id)
                   .join(Cabinet, Slot.cabinet_id == Cabinet.id)
                   .filter(Assignment.item_id.in_(ids))
                   .all())
    pos_by_item = {item_id: (cab, slot) for item_id, cab, slot in assignments}

    s = get_settings()
    label_w = mm_to_pt(s.dymo_label_w_mm)
    label_h = mm_to_pt(s.dymo_label_h_mm)
    margin_x = mm_to_pt(s.dymo_margin_x_mm)
    margin_y = mm_to_pt(s.dymo_margin_y_mm)
    font_name = (s.dymo_font_name or DEFAULT_DYMO_FONT_NAME).strip() or DEFAULT_DYMO_FONT_NAME
    font_size = s.dymo_font_size_pt or DEFAULT_DYMO_FONT_SIZE_PT
    try:
        pdfmetrics.getFont(font_name)
    except Exception:
        font_name = "Helvetica"

    buf = io.BytesIO()
    c = canvas.Canvas(buf, pagesize=(label_w, label_h))
    max_width = max(label_w - (margin_x * 2), mm_to_pt(5))
    available_height = max(label_h - (margin_y * 2), mm_to_pt(4))

    for idx, item in enumerate(items):
        if idx > 0:
            c.showPage()
        cab, slot = pos_by_item.get(item.id, (None, None))
        position_label = None
        if slot or cab:
            position_label = slot_full_label(cab, slot, for_print=True)

        raw_lines = dymo_label_lines(item, s, position_label)
        local_font_size = font_size
        rendered_lines = []
        while local_font_size >= 5.0:
            line_height = local_font_size + 0.6
            max_lines = max(int(available_height // line_height), 1)
            current_lines = []
            for text in raw_lines:
                if len(current_lines) >= max_lines:
                    break
                remaining = max_lines - len(current_lines)
                current_lines.extend(wrap_to_lines(text, font_name, local_font_size, max_width, max_lines=remaining))
            if current_lines:
                rendered_lines = current_lines
                break
            local_font_size = max(local_font_size - 0.4, 5.0)

        if not rendered_lines:
            rendered_lines = raw_lines[:1] if raw_lines else [""]

        c.setFont(font_name, local_font_size)
        y = label_h - margin_y - local_font_size
        for line in rendered_lines:
            c.drawString(margin_x, y, line)
            y -= (local_font_size + 0.6)

    c.save()
    buf.seek(0)
    return send_file(buf, as_attachment=True, download_name="etichette_dymo.pdf", mimetype="application/pdf")

@app.route("/admin/cards/pdf", methods=["POST"])
@login_required
def cards_pdf():
    try:
        from reportlab.pdfgen import canvas
        from reportlab.lib.pagesizes import landscape, portrait
        from reportlab.graphics.shapes import Drawing
        from reportlab.graphics import renderPDF
        from reportlab.lib.colors import HexColor
        from reportlab.graphics.barcode import qr as qrmod
        from reportlab.pdfbase import pdfmetrics
    except Exception:
        flash("Per la stampa cartellini installa reportlab: pip install reportlab", "danger")
        return redirect(request.referrer or url_for("admin_items"))

    slot_ids = [int(x) for x in request.form.getlist("slot_ids") if str(x).isdigit()]
    ids = request.form.getlist("item_ids")
    if slot_ids:
        ids = [
            row[0]
            for row in db.session.query(Assignment.item_id)
            .filter(Assignment.slot_id.in_(slot_ids))
            .all()
        ]
    if not ids:
        ids = [row[0] for row in db.session.query(Item.id).all()]
    items = Item.query.options(
        selectinload(Item.category),
        selectinload(Item.subtype),
        selectinload(Item.material),
        selectinload(Item.finish),
    ).filter(Item.id.in_(ids)).order_by(Item.id).all()
    if not items:
        flash("Nessun articolo valido per la stampa.", "warning")
        return redirect(request.referrer or url_for("admin_items"))

    assignments = (db.session.query(Assignment.item_id, Cabinet, Slot)
                   .join(Slot, Assignment.slot_id == Slot.id)
                   .join(Cabinet, Slot.cabinet_id == Cabinet.id)
                   .filter(Assignment.item_id.in_(ids))
                   .all())
    pos_by_item = {item_id: (cab, slot) for item_id, cab, slot in assignments}
    original_order = {item.id: idx for idx, item in enumerate(items)}

    s = get_settings()
    base_page_size = page_size_for_format(s.card_page_format)
    page_size = (landscape(base_page_size) if s.card_orientation_landscape else portrait(base_page_size))
    buf = io.BytesIO()
    c = canvas.Canvas(buf, pagesize=page_size)
    page_w, page_h = page_size

    margin_x = mm_to_pt(getattr(s, "card_margin_lr_mm", DEFAULT_CARD_MARGIN_LR_MM) or DEFAULT_CARD_MARGIN_LR_MM)
    margin_y = mm_to_pt(getattr(s, "card_margin_tb_mm", DEFAULT_CARD_MARGIN_TB_MM) or DEFAULT_CARD_MARGIN_TB_MM)
    gap = mm_to_pt(getattr(s, "card_gap_mm", DEFAULT_CARD_GAP_MM) or DEFAULT_CARD_GAP_MM)
    card_w = mm_to_pt(getattr(s, "card_w_mm", DEFAULT_CARD_W_MM) or DEFAULT_CARD_W_MM)
    card_h = mm_to_pt(getattr(s, "card_h_mm", DEFAULT_CARD_H_MM) or DEFAULT_CARD_H_MM)
    cols = int((page_w - 2 * margin_x + gap) // (card_w + gap))
    rows = int((page_h - 2 * margin_y + gap) // (card_h + gap))
    if cols < 1 or rows < 1:
        label_format_name = page_format_label(s.card_page_format)
        flash(f"Configurazione cartellini non valida rispetto al formato {label_format_name}.", "danger")
        return redirect(request.referrer or url_for("admin_items"))
    padding = mm_to_pt(getattr(s, "card_padding_mm", DEFAULT_CARD_PADDING_MM) or DEFAULT_CARD_PADDING_MM)
    include_qr = s.qr_default
    qr_box = mm_to_pt(getattr(s, "card_qr_size_mm", DEFAULT_CARD_QR_SIZE_MM) or DEFAULT_CARD_QR_SIZE_MM) if include_qr else 0
    qr_margin = mm_to_pt(getattr(s, "card_qr_margin_mm", DEFAULT_CARD_QR_MARGIN_MM) or DEFAULT_CARD_QR_MARGIN_MM) if qr_box else 0
    qr_area_width = qr_box + (qr_margin * 2 if qr_box else 0)
    base_pos_block_w = mm_to_pt(getattr(s, "card_position_width_mm", DEFAULT_CARD_POSITION_WIDTH_MM) or DEFAULT_CARD_POSITION_WIDTH_MM)
    position_font_size = getattr(s, "card_position_font_pt", DEFAULT_CARD_POSITION_FONT_PT) or DEFAULT_CARD_POSITION_FONT_PT
    position_line_height = position_font_size + 0.6

    def _fmt_mm(v):
        if v is None:
            return None
        try:
            v = float(v)
        except (TypeError, ValueError):
            return None
        if abs(v - round(v)) < 0.01:
            return str(int(round(v)))
        return f"{v:.1f}".rstrip("0").rstrip(".")

    def _card_sort_key(item: Item):
        pos_data = pos_by_item.get(item.id)
        if pos_data:
            cab, slot = pos_data
            if cab and slot:
                col_code = getattr(slot, "col_code", "") or ""
                row_num = getattr(slot, "row_num", 0) or 0
                return (0, cab.name or "", int(row_num), colcode_to_idx(col_code), original_order.get(item.id, 0))
        return (1, original_order.get(item.id, 0))

    items.sort(key=_card_sort_key)

    for idx, item in enumerate(items):
        col = idx % cols
        row = (idx // cols) % rows
        if idx > 0 and idx % (cols * rows) == 0:
            c.showPage()
        x = margin_x + col * (card_w + gap)
        y = page_h - margin_y - card_h - row * (card_h + gap)

        bg_inset = mm_to_pt(0.5)
        bg_w = max(card_w - (bg_inset * 2), 0)
        bg_h = max(card_h - (bg_inset * 2), 0)
        if bg_w > 0 and bg_h > 0:
            c.setFillColor(HexColor(item.category.color if item.category else "#000000"))
            c.rect(x + bg_inset, y + bg_inset, bg_w, bg_h, fill=1, stroke=0)

        c.setStrokeColorRGB(0, 0, 0)
        c.setLineWidth(0.3)
        c.rect(x, y, card_w, card_h, stroke=1, fill=0)
        cy = y + card_h - padding
        c.setFillColorRGB(0, 0, 0)

        pos_texts = None
        pos_block_w = base_pos_block_w
        pos_font_size = position_font_size
        pos_line_height = position_line_height
        custom_slot_label = False
        pos_data = pos_by_item.get(item.id)
        if pos_data:
            cab, slot = pos_data
            col_code = getattr(slot, "col_code", "") or ""
            row_num = getattr(slot, "row_num", None)
            label_txt = slot_label(slot, for_display=False, fallback_col=col_code, fallback_row=row_num)
            row_col_lines = []
            if row_num is not None and col_code:
                row_col_lines = [f"Rig: {int(row_num)}", f"Col: {col_code.upper()}"]
            if slot and slot.print_label_override:
                custom_slot_label = True
                pos_font_size = max(position_font_size - 1.0, 4.0)
                available_w = max(pos_block_w - mm_to_pt(1), mm_to_pt(6))
                pos_texts = wrap_to_lines(label_txt, "Helvetica-Bold", pos_font_size, available_w, max_lines=2) or [label_txt]
                pos_line_height = pos_font_size + 0.6
                combined_lines = list(pos_texts) + row_col_lines
                available_h = qr_box if qr_box else card_h - padding
                while combined_lines and (pos_line_height * len(combined_lines)) > available_h and pos_font_size > 4.0:
                    pos_font_size = max(pos_font_size - 0.4, 4.0)
                    pos_line_height = pos_font_size + 0.6
                    pos_texts = wrap_to_lines(label_txt, "Helvetica-Bold", pos_font_size, available_w, max_lines=2) or [label_txt]
                    combined_lines = list(pos_texts) + row_col_lines
                pos_texts = combined_lines or row_col_lines
                if pos_texts:
                    max_width = max(pdfmetrics.stringWidth(txt, "Helvetica-Bold", pos_font_size) for txt in pos_texts)
                    pos_block_w = max(pos_block_w, max_width + mm_to_pt(1))
            elif row_col_lines:
                pos_texts = row_col_lines
                required_w = max(pdfmetrics.stringWidth(txt, "Helvetica-Bold", pos_font_size) for txt in pos_texts) + mm_to_pt(1)
                pos_block_w = max(pos_block_w, required_w)
            elif label_txt:
                pos_texts = [label_txt]
                required_w = pdfmetrics.stringWidth(label_txt, "Helvetica-Bold", pos_font_size) + mm_to_pt(1)
                pos_block_w = max(pos_block_w, required_w)

        text_right_edge = x + card_w - padding - qr_area_width - (pos_block_w if pos_texts else 0)
        text_area_w = max(text_right_edge - (x + padding), mm_to_pt(10))

        title_font_size = 12
        title_leading = 11
        title_lines = wrap_to_lines(
            auto_name_for(item),
            "Helvetica-Bold",
            title_font_size,
            text_area_w,
            max_lines=2,
        )
        c.setFont("Helvetica-Bold", title_font_size)
        for ln in title_lines:
            cy -= title_leading
            c.drawString(x + padding, cy, ln)
            cy -= 2

        if pos_texts:
            pos_x = x + card_w - padding - qr_area_width - pos_block_w
            if qr_box:
                block_height = pos_line_height * len(pos_texts)
                start_y = y + qr_margin + max((qr_box - block_height) / 2, 0) + block_height - pos_font_size
            else:
                start_y = y + card_h - padding - pos_font_size
            if custom_slot_label:
                start_y -= mm_to_pt(0.5)
            c.setFont("Helvetica-Bold", pos_font_size)
            line_y = start_y
            for txt in pos_texts:
                c.drawString(pos_x, line_y, txt)
                line_y -= pos_line_height

        details = []
        dim = _fmt_mm(item.outer_d_mm if not (is_screw(item) or is_standoff(item) or is_spacer(item)) else item.length_mm)
        if dim:
            prefix = "L" if (is_screw(item) or is_standoff(item) or is_spacer(item)) else "Øe"
            details.append(f"{prefix}: {dim} mm")
        if item.inner_d_mm:
            details.append(f"Øi: {_fmt_mm(item.inner_d_mm)} mm")
        thickness_val = unified_thickness_value(item)
        if thickness_val:
            details.append(f"Spessore: {_fmt_mm(thickness_val)} mm")
        if item.material:
            details.append(f"Materiale: {item.material.name}")
        if item.finish:
            details.append(f"Finitura: {item.finish.name}")
        if details:
            c.setFont("Helvetica", 9.5)
            for det in details:
                next_y = cy - 11
                if next_y < y + padding:
                    break
                cy = next_y
                c.drawString(x + padding, cy, det)
            cy -= 4

        if item.description:
            desc_lines = wrap_to_lines(item.description, "Helvetica-Oblique", 9, text_area_w, max_lines=3)
            if desc_lines:
                c.setFont("Helvetica-Oblique", 9)
                for ln in desc_lines:
                    next_y = cy - 11
                    if next_y < y + padding:
                        break
                    cy = next_y
                    c.drawString(x + padding, cy, ln)
                cy -= 2

        if qr_box:
            try:
                if s.qr_base_url:
                    url = f"{s.qr_base_url.rstrip('/')}/api/items/{item.id}.json"
                else:
                    url = f"{request.host_url.rstrip('/')}/api/items/{item.id}.json"
                qr_code = qrmod.QrCodeWidget(url)
                bounds = qr_code.getBounds()
                w = bounds[2] - bounds[0]
                h = bounds[3] - bounds[1]
                scale = min(qr_box / w, qr_box / h)
                d = Drawing(w, h)
                d.add(qr_code)
                c.saveState()
                c.translate(x + card_w - padding - qr_box - qr_margin, y + qr_margin)
                c.scale(scale, scale)
                renderPDF.draw(d, c, 0, 0)
                c.restoreState()
            except Exception:
                pass

    c.save()
    buf.seek(0)
    return send_file(buf, as_attachment=True, download_name="cartellini.pdf", mimetype="application/pdf")
# ===================== INIT / SEED =====================

def seed_if_empty_or_missing():
    ensure_settings_columns()
    ensure_item_columns()
    ensure_category_columns()
    ensure_slot_columns()
    ensure_user_columns()
    ensure_auth_defaults()
    if not Settings.query.get(1):
        db.session.add(Settings(
            id=1,
            label_w_mm=DEFAULT_LABEL_W_MM, label_h_mm=DEFAULT_LABEL_H_MM,
            margin_tb_mm=DEFAULT_MARG_TB_MM, margin_lr_mm=DEFAULT_MARG_LR_MM,
            gap_mm=DEFAULT_GAP_MM, label_padding_mm=DEFAULT_LABEL_PADDING_MM,
            label_qr_size_mm=DEFAULT_LABEL_QR_SIZE_MM, label_qr_margin_mm=DEFAULT_LABEL_QR_MARGIN_MM,
            label_position_width_mm=DEFAULT_LABEL_POSITION_WIDTH_MM,
            label_position_font_pt=DEFAULT_LABEL_POSITION_FONT_PT,
            label_page_format=DEFAULT_LABEL_PAGE_FORMAT,
            card_w_mm=DEFAULT_CARD_W_MM, card_h_mm=DEFAULT_CARD_H_MM,
            card_margin_tb_mm=DEFAULT_CARD_MARGIN_TB_MM, card_margin_lr_mm=DEFAULT_CARD_MARGIN_LR_MM,
            card_gap_mm=DEFAULT_CARD_GAP_MM, card_padding_mm=DEFAULT_CARD_PADDING_MM,
            card_qr_size_mm=DEFAULT_CARD_QR_SIZE_MM, card_qr_margin_mm=DEFAULT_CARD_QR_MARGIN_MM,
            card_position_width_mm=DEFAULT_CARD_POSITION_WIDTH_MM,
            card_position_font_pt=DEFAULT_CARD_POSITION_FONT_PT,
            card_gap_h_mm=DEFAULT_CARD_GAP_H_MM, card_gap_v_mm=DEFAULT_CARD_GAP_V_MM,
            card_page_format=DEFAULT_CARD_PAGE_FORMAT,
            orientation_landscape=DEFAULT_ORIENTATION_LANDSCAPE,
            card_orientation_landscape=DEFAULT_CARD_ORIENTATION_LANDSCAPE,
            qr_default=DEFAULT_QR_DEFAULT, qr_base_url=DEFAULT_QR_BASE_URL
        ))
    thread_standards = [
        ("M", "Metrico", 10),
        ("UNC", "UNC", 20),
        ("UNF", "UNF", 30),
    ]
    for code, label, order in thread_standards:
        if not ThreadStandard.query.filter_by(code=code).first():
            db.session.add(ThreadStandard(code=code, label=label, sort_order=order))

    # categorie/materiali/finiture predefinite solo su db vuoto
    has_categories = Category.query.count() > 0
    has_materials = Material.query.count() > 0
    has_finishes = Finish.query.count() > 0

    if not has_categories:
        defaults = [
            ("Viti","#2E7D32"), ("Dadi","#1565C0"), ("Rondelle","#F9A825"), ("Torrette","#6A1B9A"),
            ("Grani","#8E24AA"), ("Prigionieri","#3949AB"), ("Inserti e rivetti","#00897B"),
            ("Seeger e spine","#5D4037"), ("Distanziali","#00796B"), ("Boccole","#546E7A"), ("O-Ring","#D84315")
        ]
        for name,color in defaults:
            if not Category.query.filter_by(name=name).first():
                db.session.add(Category(name=name, color=color))
    if not has_materials:
        for m in ["Acciaio","Inox A2","Inox A4","Ottone","Alluminio","Rame","Nylon","Ottone nichelato","Bronzo","PTFE","EPDM","Viton","Silicone"]:
            if not Material.query.filter_by(name=m).first():
                db.session.add(Material(name=m))
    if not has_finishes:
        for f in ["Zincato bianco","Zincato nero","Brunitura","Nichelato","Grezzo","Anodizzato"]:
            if not Finish.query.filter_by(name=f).first():
                db.session.add(Finish(name=f))
    db.session.commit()

    standards_by_code = {s.code: s for s in ThreadStandard.query.all()}
    sizes_by_standard = {
        "M": ["M2","M2.5","M3","M4","M5","M6","M8","M10","M12","M14","M16"],
        "UNC": ["#2-56","#4-40","#6-32","#8-32","#10-24","1/4-20","5/16-18","3/8-16","1/2-13"],
        "UNF": ["#2-64","#4-48","#6-40","#8-36","#10-32","1/4-28","5/16-24","3/8-24","1/2-20"],
    }
    for code, values in sizes_by_standard.items():
        standard = standards_by_code.get(code)
        if not standard:
            continue
        for idx, value in enumerate(values, start=1):
            exists = ThreadSize.query.filter_by(standard_id=standard.id, value=value).first()
            if not exists:
                db.session.add(ThreadSize(standard_id=standard.id, value=value, sort_order=idx * 10))

    cat = {c.name: c.id for c in Category.query.all()}

    # Viti — sottotipi (forme testa)
    for nm in ["Svasata (TSP)","Cilindrica","Bombata/Lenticolare","Piatta/Ribassata","Esagonale","Flangiata","Svasata ovale"]:
        if cat.get("Viti") and not Subtype.query.filter_by(category_id=cat["Viti"], name=nm).first():
            db.session.add(Subtype(category_id=cat["Viti"], name=nm))

    # Dadi — sottotipi
    for nm in ["Esagonale","Autobloccante (nylon)","Cieco","Basso (jam)","Flangiato"]:
        if cat.get("Dadi") and not Subtype.query.filter_by(category_id=cat["Dadi"], name=nm).first():
            db.session.add(Subtype(category_id=cat["Dadi"], name=nm))

    # Rondelle
    for nm in ["Piana","Grower (molla)","Dentellata esterna","Dentellata interna","Larga (fender)","Belleville (a tazza)"]:
        if cat.get("Rondelle") and not Subtype.query.filter_by(category_id=cat["Rondelle"], name=nm).first():
            db.session.add(Subtype(category_id=cat["Rondelle"], name=nm))

    # Torrette — forme
    for nm in ["Esagonale","Cilindrica","Flangiata","Snap-in","Press-fit","Adesiva"]:
        if cat.get("Torrette") and not Subtype.query.filter_by(category_id=cat["Torrette"], name=nm).first():
            db.session.add(Subtype(category_id=cat["Torrette"], name=nm))

    # Grani (viti senza testa) — punte
    for nm in ["Punta piana","A coppa","Conica","Dog point"]:
        if cat.get("Grani") and not Subtype.query.filter_by(category_id=cat["Grani"], name=nm).first():
            db.session.add(Subtype(category_id=cat["Grani"], name=nm))

    # Prigionieri
    for nm in ["Doppio filetto","Filettato totale","Filettatura parziale"]:
        if cat.get("Prigionieri") and not Subtype.query.filter_by(category_id=cat["Prigionieri"], name=nm).first():
            db.session.add(Subtype(category_id=cat["Prigionieri"], name=nm))

    # Inserti e rivetti
    for nm in ["Inserto filettato (rivnut)","Inserto filettato (press-fit)","Rivetto cieco standard","Rivetto cieco multigrip"]:
        if cat.get("Inserti e rivetti") and not Subtype.query.filter_by(category_id=cat["Inserti e rivetti"], name=nm).first():
            db.session.add(Subtype(category_id=cat["Inserti e rivetti"], name=nm))

    # Seeger e spine
    for nm in ["Seeger interno","Seeger esterno","Spina elastica","Spina cilindrica","Anello elastico a filo"]:
        if cat.get("Seeger e spine") and not Subtype.query.filter_by(category_id=cat["Seeger e spine"], name=nm).first():
            db.session.add(Subtype(category_id=cat["Seeger e spine"], name=nm))

    # Distanziali (lisci)
    for nm in ["Liscio cilindrico","Liscio esagonale"]:
        if cat.get("Distanziali") and not Subtype.query.filter_by(category_id=cat["Distanziali"], name=nm).first():
            db.session.add(Subtype(category_id=cat["Distanziali"], name=nm))

    # Boccole
    for nm in ["Rettificata","Autolubrificante (sinterizzata)","Polimerica (PA/PTFE)"]:
        if cat.get("Boccole") and not Subtype.query.filter_by(category_id=cat["Boccole"], name=nm).first():
            db.session.add(Subtype(category_id=cat["Boccole"], name=nm))

    # O-Ring
    for nm in ["O-Ring","X-Ring (quad)"]:
        if cat.get("O-Ring") and not Subtype.query.filter_by(category_id=cat["O-Ring"], name=nm).first():
            db.session.add(Subtype(category_id=cat["O-Ring"], name=nm))

    db.session.commit()

    # seed minimo ubicazione/cassettiera
    if not Location.query.first():
        loc = Location(name="Parete A")
        db.session.add(loc); db.session.flush()
        cab = Cabinet(location_id=loc.id, name="Cassettiera 1", rows_max=128, cols_max="ZZ", compartments_per_slot=6)
        db.session.add(cab); db.session.commit()

def init_db():
    with app.app_context():
        db.create_all()
        seed_if_empty_or_missing()

# ===================== MAIN =====================
if __name__ == "__main__":
    init_db()
    run_startup_backup()
    app.run(debug=True, host="0.0.0.0")
