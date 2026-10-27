# ============================================================
# ONLINE VOTING SYSTEM
# Flask + SQLite
# ============================================================
#
# FEATURES
# ------------------------------------------------------------
# User Registration
# Aadhaar Validation
# Duplicate Aadhaar Prevention
# Mobile Validation
# Duplicate Mobile Prevention
# Duplicate Email Prevention (case-insensitive)
# 18+ Age Validation
# Camera Photo Validation
# User Login
# Forgot Password
#
# Admin Login
# Multiple Elections
# Election-specific Candidates
# Election-specific Votes
# Election-specific Eligibility
# Election-specific Schedule
# Election-specific Blockchain
#
# All India Election
# State Election
# District Election
#
# Election Results
# Winner
# Voted / Not Voted
# Election Archive
# Election Delete
#
# Existing Users Preserved
# Existing Database Preserved
#
# IMPORTANT:
# voting_system.db is NEVER deleted automatically.
# Database migration is performed automatically.
# ============================================================


# ============================================================
# IMPORTS
# ============================================================

import os
import re
import io
import base64
import hashlib
import secrets
import smtplib
import sqlite3
import json
import urllib.request
import urllib.error

from datetime import datetime, date, timedelta
from email.message import EmailMessage

from flask import (
    Flask,
    render_template,
    request,
    redirect,
    url_for,
    session,
    flash,
    jsonify
)

from werkzeug.security import (
    generate_password_hash,
    check_password_hash
)

from werkzeug.utils import secure_filename


# ============================================================
# OPTIONAL OPENCV
# ============================================================

try:
    import cv2
    import numpy as np

    OPENCV_AVAILABLE = True

except ImportError:

    cv2 = None
    np = None

    OPENCV_AVAILABLE = False


# ============================================================
# FLASK APP
# ============================================================

app = Flask(__name__)

print(
    "Template folder:",
    app.template_folder
)

app.secret_key = os.environ.get(
    "FLASK_SECRET_KEY",
    "change-this-secret-key-in-production"
)

app.config["MAX_CONTENT_LENGTH"] = (
    5 * 1024 * 1024
)


# ============================================================
# BASE PATHS
# ============================================================

BASE_DIR = os.path.abspath(
    os.path.dirname(__file__)
)

DATABASE_DIR = os.path.join(BASE_DIR, "database")

# Prefer an existing database instead of silently creating a new empty one.
# This prevents the results page from showing 0 when the real database is
# stored at the project root rather than in the database/ folder.
_DATABASE_CANDIDATES = [
    os.path.join(DATABASE_DIR, "voting_system.db"),
    os.path.join(BASE_DIR, "voting_system.db"),
    os.path.join(BASE_DIR, "instance", "voting_system.db"),
]

def _database_score(path):
    """Prefer the existing SQLite file that contains the project's real data."""
    if not os.path.isfile(path):
        return (-1, -1, -1)
    try:
        conn = sqlite3.connect(path, timeout=2)
        try:
            tables = {row[0] for row in conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table'")}
            counts = []
            for table in ("users", "elections", "election_votes", "election_candidates"):
                if table in tables:
                    # Table names are selected only from the fixed allowlist above.
                    counts.append(int(conn.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0]))
                else:
                    counts.append(0)
            # Vote records and user/election data matter more than file size.
            return (sum(counts), len(tables), os.path.getsize(path))
        finally:
            conn.close()
    except (sqlite3.Error, OSError):
        return (0, 0, 0)

_existing_databases = [path for path in _DATABASE_CANDIDATES if os.path.isfile(path)]
DATABASE = max(_existing_databases, key=_database_score) if _existing_databases else _DATABASE_CANDIDATES[0]

print("\n========== DATABASE DEBUG ==========")
print("Selected database:", os.path.abspath(DATABASE))
print("Database exists:", os.path.isfile(DATABASE))
print("Database score:", _database_score(DATABASE))
print("====================================\n")

UPLOAD_FOLDER = os.path.join(BASE_DIR, "static", "uploads", "voters")
SYMBOL_UPLOAD_FOLDER = os.path.join(BASE_DIR, "static", "uploads", "symbols")

os.makedirs(DATABASE_DIR, exist_ok=True)
os.makedirs(UPLOAD_FOLDER, exist_ok=True)
os.makedirs(SYMBOL_UPLOAD_FOLDER, exist_ok=True)

app.config["UPLOAD_FOLDER"] = (
    UPLOAD_FOLDER
)


# ============================================================
# CONSTANTS
# ============================================================

COUNTRY = "India"

ADMIN_USERNAME = "admin"

ADMIN_DEFAULT_PASSWORD = "admin123"

ALLOWED_IMAGE_EXTENSIONS = {
    "jpg",
    "jpeg",
    "png",
    "webp"
}


# ============================================================
# INDIAN STATES / UNION TERRITORIES
# ============================================================

INDIAN_STATES = [

    "Andhra Pradesh",
    "Arunachal Pradesh",
    "Assam",
    "Bihar",
    "Chhattisgarh",
    "Goa",
    "Gujarat",
    "Haryana",
    "Himachal Pradesh",
    "Jharkhand",
    "Karnataka",
    "Kerala",
    "Madhya Pradesh",
    "Maharashtra",
    "Manipur",
    "Meghalaya",
    "Mizoram",
    "Nagaland",
    "Odisha",
    "Punjab",
    "Rajasthan",
    "Sikkim",
    "Tamil Nadu",
    "Telangana",
    "Tripura",
    "Uttar Pradesh",
    "Uttarakhand",
    "West Bengal",

    "Andaman and Nicobar Islands",
    "Chandigarh",
    "Dadra and Nagar Haveli and Daman and Diu",
    "Delhi",
    "Jammu and Kashmir",
    "Ladakh",
    "Lakshadweep",
    "Puducherry"
]


# ============================================================
# DISTRICTS
# ============================================================

FALLBACK_INDIA_DISTRICTS = {

    "Andhra Pradesh": [
        "Alluri Sitharama Raju",
        "Anakapalli",
        "Anantapur",
        "Annamayya",
        "Bapatla",
        "Chittoor",
        "Dr. B.R. Ambedkar Konaseema",
        "East Godavari",
        "Eluru",
        "Guntur",
        "Kakinada",
        "Krishna",
        "Kurnool",
        "Nandyal",
        "NTR",
        "Palnadu",
        "Parvathipuram Manyam",
        "Prakasam",
        "Sri Potti Sriramulu Nellore",
        "Sri Sathya Sai",
        "Srikakulam",
        "Tirupati",
        "Visakhapatnam",
        "Vizianagaram",
        "West Godavari",
        "YSR Kadapa"
    ],

    "Arunachal Pradesh": [
        "Anjaw",
        "Changlang",
        "Dibang Valley",
        "East Kameng",
        "East Siang",
        "Kamle",
        "Kra Daadi",
        "Kurung Kumey",
        "Lepa Rada",
        "Lohit",
        "Longding",
        "Lower Dibang Valley",
        "Lower Siang",
        "Lower Subansiri",
        "Namsai",
        "Pakke Kessang",
        "Papum Pare",
        "Shi Yomi",
        "Siang",
        "Tawang",
        "Tirap",
        "Upper Siang",
        "Upper Subansiri",
        "West Kameng",
        "West Siang"
    ],

    "Assam": [
        "Baksa",
        "Barpeta",
        "Biswanath",
        "Bongaigaon",
        "Cachar",
        "Charaideo",
        "Chirang",
        "Darrang",
        "Dhemaji",
        "Dhubri",
        "Dibrugarh",
        "Dima Hasao",
        "Goalpara",
        "Golaghat",
        "Hailakandi",
        "Hojai",
        "Jorhat",
        "Kamrup",
        "Kamrup Metropolitan",
        "Karbi Anglong",
        "Karimganj",
        "Kokrajhar",
        "Lakhimpur",
        "Majuli",
        "Morigaon",
        "Nagaon",
        "Nalbari",
        "Sivasagar",
        "Sonitpur",
        "South Salmara-Mankachar",
        "Tamulpur",
        "Tinsukia",
        "Udalguri",
        "West Karbi Anglong"
    ],

    "Bihar": [
        "Araria",
        "Arwal",
        "Aurangabad",
        "Banka",
        "Begusarai",
        "Bhagalpur",
        "Bhojpur",
        "Buxar",
        "Darbhanga",
        "East Champaran",
        "Gaya",
        "Gopalganj",
        "Jamui",
        "Jehanabad",
        "Kaimur",
        "Katihar",
        "Khagaria",
        "Kishanganj",
        "Lakhisarai",
        "Madhepura",
        "Madhubani",
        "Munger",
        "Muzaffarpur",
        "Nalanda",
        "Nawada",
        "Patna",
        "Purnia",
        "Rohtas",
        "Saharsa",
        "Samastipur",
        "Saran",
        "Sheikhpura",
        "Sheohar",
        "Sitamarhi",
        "Siwan",
        "Supaul",
        "Vaishali",
        "West Champaran"
    ],

    "Chhattisgarh": [],
    "Goa": [],
    "Gujarat": [],
    "Haryana": [],
    "Himachal Pradesh": [],
    "Jharkhand": [],
    "Karnataka": [],
    "Kerala": [],
    "Madhya Pradesh": [],
    "Maharashtra": [],
    "Manipur": [],
    "Meghalaya": [],
    "Mizoram": [],
    "Nagaland": [],
    "Odisha": [],
    "Punjab": [],
    "Rajasthan": [],
    "Sikkim": [],
    "Tamil Nadu": [],
    "Telangana": [],
    "Tripura": [],
    "Uttar Pradesh": [],
    "Uttarakhand": [],
    "West Bengal": [],

    "Andaman and Nicobar Islands": [],

    "Chandigarh": [
        "Chandigarh"
    ],

    "Dadra and Nagar Haveli and Daman and Diu": [],

    "Delhi": [
        "Central Delhi",
        "East Delhi",
        "New Delhi",
        "North Delhi",
        "North East Delhi",
        "North West Delhi",
        "Shahdara",
        "South Delhi",
        "South East Delhi",
        "South West Delhi",
        "West Delhi"
    ],

    "Jammu and Kashmir": [],

    "Ladakh": [],

    "Lakshadweep": [],

    "Puducherry": [
        "Karaikal",
        "Mahe",
        "Puducherry",
        "Yanam"
    ]
}


# ============================================================
# LOAD COMPLETE DISTRICT LIST FOR ALL STATES / UNION TERRITORIES
# ============================================================
# The data source contains the state/UT names and their district names.
# It is downloaded once and cached beside this Python file. On later
# starts, the cached JSON is used, so the app can work without internet.
# If both download and cache are unavailable, the fallback list above is used.

DISTRICT_DATA_URL = (
    "https://raw.githubusercontent.com/"
    "codingmation/indian-states-districts/main/data/india_states_districts.json"
)
DISTRICT_CACHE_FILE = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "india_states_districts.json"
)


def load_india_districts():
    """Return a mapping of every Indian state/UT to its district names."""
    data = None

    # Prefer the local cache so the app does not need internet every time.
    try:
        if os.path.isfile(DISTRICT_CACHE_FILE):
            with open(DISTRICT_CACHE_FILE, "r", encoding="utf-8") as file:
                data = json.load(file)
    except (OSError, json.JSONDecodeError):
        data = None

    # Download the list if the cache is missing or invalid.
    if not isinstance(data, list) or not data:
        try:
            req = urllib.request.Request(
                DISTRICT_DATA_URL,
                headers={"User-Agent": "OnlineVotingSystem/1.0"},
            )
            with urllib.request.urlopen(req, timeout=8) as response:
                data = json.loads(response.read().decode("utf-8"))

            if isinstance(data, list) and data:
                try:
                    with open(DISTRICT_CACHE_FILE, "w", encoding="utf-8") as file:
                        json.dump(data, file, ensure_ascii=False, indent=2)
                except OSError:
                    # A read-only folder should not stop the app from starting.
                    pass
        except (OSError, urllib.error.URLError, json.JSONDecodeError, TimeoutError):
            data = None

    if not isinstance(data, list) or not data:
        print(
            "WARNING: Could not load the complete district dataset. "
            "Using the built-in fallback list. Check internet access or place "
            "india_states_districts.json beside this Python file."
        )
        return FALLBACK_INDIA_DISTRICTS

    loaded = {}
    for state_record in data:
        if not isinstance(state_record, dict):
            continue
        state_name = state_record.get("name")
        districts = state_record.get("districts", [])
        if not isinstance(state_name, str) or not isinstance(districts, list):
            continue
        district_names = [
            item.get("name")
            for item in districts
            if isinstance(item, dict) and isinstance(item.get("name"), str)
        ]
        if district_names:
            loaded[state_name] = district_names

    # Keep the app's expected state names and fill any source naming gaps
    # from the built-in list, without overwriting the complete downloaded list.
    for state_name in INDIAN_STATES:
        if state_name not in loaded or not loaded[state_name]:
            loaded[state_name] = FALLBACK_INDIA_DISTRICTS.get(state_name, [])

    return loaded


INDIA_DISTRICTS = load_india_districts()


# ============================================================
# DEFAULT LEGACY CANDIDATES
# ============================================================

DEFAULT_CANDIDATES = []


# ============================================================
# DATABASE CONNECTION
# ============================================================

def get_db():

    conn = sqlite3.connect(
        DATABASE,
        timeout=30
    )

    conn.row_factory = sqlite3.Row

    conn.execute(
        "PRAGMA foreign_keys = ON"
    )

    return conn


# ============================================================
# DATABASE HELPERS
# ============================================================

def table_exists(
    conn,
    table_name
):

    row = conn.execute(
        """
        SELECT name
        FROM sqlite_master
        WHERE type = 'table'
        AND name = ?
        """,
        (
            table_name,
        )
    ).fetchone()

    return row is not None


def column_exists(
    conn,
    table_name,
    column_name
):

    rows = conn.execute(
        f"PRAGMA table_info({table_name})"
    ).fetchall()

    return any(
        row["name"] == column_name
        for row in rows
    )


def add_column_if_missing(
    conn,
    table_name,
    column_name,
    definition
):

    if not column_exists(
        conn,
        table_name,
        column_name
    ):

        conn.execute(
            f"""
            ALTER TABLE {table_name}
            ADD COLUMN {column_name} {definition}
            """
        )


# ============================================================
# DATABASE INITIALIZATION / MIGRATION
# ============================================================

def init_db():

    conn = get_db()

    try:

        # ====================================================
        # LEGACY CANDIDATES
        # ====================================================

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS candidates
            (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                party TEXT,
                party_symbol TEXT,
                votes INTEGER DEFAULT 0
            )
            """
        )

        # ====================================================
        # USERS
        # ====================================================

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS users
            (
                id INTEGER PRIMARY KEY AUTOINCREMENT,

                name TEXT NOT NULL,

                father_name TEXT,

                dob TEXT,

                aadhaar TEXT,

                aadhaar_hash TEXT,

                mobile TEXT,

                email TEXT,

                password TEXT,

                address TEXT,

                state TEXT,

                district TEXT,

                country TEXT DEFAULT 'India',

                photo TEXT,

                eligible INTEGER DEFAULT 1,

                has_voted INTEGER DEFAULT 0,

                voted_candidate_id INTEGER,

                registration_date TEXT,

                FOREIGN KEY
                (
                    voted_candidate_id
                )
                REFERENCES candidates(id)
            )
            """
        )

        # ====================================================
        # ADMIN
        # ====================================================

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS admin
            (
                id INTEGER PRIMARY KEY AUTOINCREMENT,

                username TEXT UNIQUE NOT NULL,

                password TEXT NOT NULL,

                email TEXT
            )
            """
        )

        # ====================================================
        # LEGACY BLOCKCHAIN
        # ====================================================

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS blockchain
            (
                id INTEGER PRIMARY KEY AUTOINCREMENT,

                voter_hash TEXT NOT NULL,

                candidate_name TEXT NOT NULL,

                timestamp TEXT NOT NULL,

                previous_hash TEXT NOT NULL,

                block_hash TEXT NOT NULL
            )
            """
        )

        # ====================================================
        # LEGACY VOTING SETTINGS
        # ====================================================

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS voting_settings
            (
                id INTEGER PRIMARY KEY CHECK(id = 1),

                start_datetime TEXT,

                duration_seconds INTEGER DEFAULT 0,

                created_at TEXT,

                updated_at TEXT
            )
            """
        )

        # ====================================================
        # LEGACY ELIGIBILITY
        # ====================================================

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS voting_eligibility
            (
                id INTEGER PRIMARY KEY CHECK(id = 1),

                scope TEXT DEFAULT 'all_india',

                state TEXT,

                district TEXT,

                updated_at TEXT
            )
            """
        )

        # ====================================================
        # PASSWORD REQUESTS
        # ====================================================

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS password_requests
            (
                id INTEGER PRIMARY KEY AUTOINCREMENT,

                name TEXT,

                father_name TEXT,

                email TEXT,

                mobile TEXT,

                aadhaar TEXT,

                status TEXT DEFAULT 'pending',

                temporary_password TEXT,

                request_date TEXT,

                processed_date TEXT
            )
            """
        )

        # ====================================================
        # USER MIGRATIONS
        # ====================================================

        user_columns = {

            "father_name":
                "TEXT",

            "dob":
                "TEXT",

            "aadhaar":
                "TEXT",

            "aadhaar_hash":
                "TEXT",

            "mobile":
                "TEXT",

            "email":
                "TEXT",

            "password":
                "TEXT",

            "address":
                "TEXT",

            "state":
                "TEXT",

            "district":
                "TEXT",

            "country":
                "TEXT DEFAULT 'India'",

            "photo":
                "TEXT",

            "eligible":
                "INTEGER DEFAULT 1",

            "has_voted":
                "INTEGER DEFAULT 0",

            "voted_candidate_id":
                "INTEGER",

            "registration_date":
                "TEXT"
        }

        for column_name, definition in (
            user_columns.items()
        ):

            add_column_if_missing(
                conn,
                "users",
                column_name,
                definition
            )

        # ====================================================
        # CANDIDATE MIGRATIONS
        # ====================================================

        add_column_if_missing(
            conn,
            "candidates",
            "party",
            "TEXT"
        )

        add_column_if_missing(
            conn,
            "candidates",
            "party_symbol",
            "TEXT"
        )

        add_column_if_missing(
            conn,
            "candidates",
            "votes",
            "INTEGER DEFAULT 0"
        )

        # ====================================================
        # INDEXES
        # ====================================================

        try:

            conn.execute(
                """
                CREATE UNIQUE INDEX IF NOT EXISTS
                idx_users_aadhaar_unique
                ON users(aadhaar)
                """
            )

        except sqlite3.IntegrityError:

            print(
                "Warning: duplicate Aadhaar values exist."
            )

        try:

            conn.execute(
                """
                CREATE UNIQUE INDEX IF NOT EXISTS
                idx_users_email_unique
                ON users(email)
                WHERE email IS NOT NULL AND TRIM(email) != ''
                """
            )

        except sqlite3.IntegrityError:

            print(
                "Warning: duplicate email values exist; registration checks will still reject duplicates."
            )

        # Prevent duplicate mobile numbers for new registrations.
        # Existing duplicate rows, if any, must be reviewed manually before
        # SQLite can enforce this unique index.
        try:

            conn.execute(
                """
                CREATE UNIQUE INDEX IF NOT EXISTS
                idx_users_mobile_unique
                ON users(mobile)
                WHERE mobile IS NOT NULL AND TRIM(mobile) != ''
                """
            )

        except sqlite3.IntegrityError:

            print(
                "Warning: duplicate mobile values exist; registration checks will still reject duplicates."
            )

        # Email addresses are treated case-insensitively (e.g. A@B.com = a@b.com).
        try:

            conn.execute(
                """
                CREATE UNIQUE INDEX IF NOT EXISTS
                idx_users_email_lower_unique
                ON users(LOWER(TRIM(email)))
                WHERE email IS NOT NULL AND TRIM(email) != ''
                """
            )

        except sqlite3.IntegrityError:

            print(
                "Warning: case-insensitive duplicate email values exist; registration checks will still reject duplicates."
            )

        conn.execute(
            """
            CREATE INDEX IF NOT EXISTS
            idx_users_aadhaar_hash
            ON users(aadhaar_hash)
            """
        )

        # ====================================================
        # BACKFILL AADHAAR HASH
        # ====================================================

        users_without_hash = conn.execute(
            """
            SELECT id, aadhaar
            FROM users
            WHERE
                aadhaar IS NOT NULL
                AND aadhaar != ''
                AND
                (
                    aadhaar_hash IS NULL
                    OR aadhaar_hash = ''
                )
            """
        ).fetchall()

        for user in users_without_hash:

            aadhaar_hash = hashlib.sha256(
                user["aadhaar"].encode(
                    "utf-8"
                )
            ).hexdigest()

            conn.execute(
                """
                UPDATE users
                SET aadhaar_hash = ?
                WHERE id = ?
                """,
                (
                    aadhaar_hash,
                    user["id"]
                )
            )

        # ====================================================
        # DEFAULT ADMIN
        # ====================================================

        admin = conn.execute(
            """
            SELECT id
            FROM admin
            WHERE username = ?
            """,
            (
                ADMIN_USERNAME,
            )
        ).fetchone()

        if not admin:

            conn.execute(
                """
                INSERT INTO admin
                (
                    username,
                    password,
                    email
                )
                VALUES (?, ?, ?)
                """,
                (
                    ADMIN_USERNAME,

                    generate_password_hash(
                        ADMIN_DEFAULT_PASSWORD
                    ),

                    "subhamojha101@gmail.com"
                )
            )

        # ====================================================
        # LEGACY SETTINGS
        # ====================================================

        settings = conn.execute(
            """
            SELECT id
            FROM voting_settings
            WHERE id = 1
            """
        ).fetchone()

        if not settings:

            now = datetime.now().isoformat()

            conn.execute(
                """
                INSERT INTO voting_settings
                (
                    id,
                    start_datetime,
                    duration_seconds,
                    created_at,
                    updated_at
                )
                VALUES
                (
                    1,
                    NULL,
                    0,
                    ?,
                    ?
                )
                """,
                (
                    now,
                    now
                )
            )

        eligibility = conn.execute(
            """
            SELECT id
            FROM voting_eligibility
            WHERE id = 1
            """
        ).fetchone()

        if not eligibility:

            conn.execute(
                """
                INSERT INTO voting_eligibility
                (
                    id,
                    scope,
                    state,
                    district,
                    updated_at
                )
                VALUES
                (
                    1,
                    'all_india',
                    NULL,
                    NULL,
                    ?
                )
                """,
                (
                    datetime.now().isoformat(),
                )
            )

        # ====================================================
        # ELECTIONS
        # ====================================================

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS elections
            (
                id INTEGER PRIMARY KEY AUTOINCREMENT,

                name TEXT NOT NULL,

                description TEXT,

                election_type TEXT DEFAULT 'general',

                scope TEXT DEFAULT 'all_india',

                state TEXT,

                district TEXT,

                start_datetime TEXT,

                duration_seconds INTEGER DEFAULT 0,

                status TEXT DEFAULT 'draft',

                archived INTEGER DEFAULT 0,

                created_at TEXT,

                updated_at TEXT
            )
            """
        )

        # ====================================================
        # ELECTION CANDIDATES
        # ====================================================

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS election_candidates
            (
                id INTEGER PRIMARY KEY AUTOINCREMENT,

                election_id INTEGER NOT NULL,

                name TEXT NOT NULL,

                party TEXT,

                party_symbol TEXT,

                created_at TEXT,

                FOREIGN KEY
                (
                    election_id
                )
                REFERENCES elections(id)
                ON DELETE CASCADE
            )
            """
        )

        # ====================================================
        # ELECTION VOTES
        # ====================================================

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS election_votes
            (
                id INTEGER PRIMARY KEY AUTOINCREMENT,

                election_id INTEGER NOT NULL,

                user_id INTEGER NOT NULL,

                candidate_id INTEGER NOT NULL,

                timestamp TEXT NOT NULL,

                voter_hash TEXT NOT NULL,

                UNIQUE
                (
                    election_id,
                    user_id
                ),

                FOREIGN KEY
                (
                    election_id
                )
                REFERENCES elections(id)
                ON DELETE CASCADE,

                FOREIGN KEY
                (
                    user_id
                )
                REFERENCES users(id)
                ON DELETE CASCADE,

                FOREIGN KEY
                (
                    candidate_id
                )
                REFERENCES election_candidates(id)
                ON DELETE CASCADE
            )
            """
        )

        # ====================================================
        # ELECTION BLOCKCHAIN
        # ====================================================

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS election_blockchain
            (
                id INTEGER PRIMARY KEY AUTOINCREMENT,

                election_id INTEGER NOT NULL,

                vote_id INTEGER,

                voter_hash TEXT NOT NULL,

                candidate_name TEXT NOT NULL,

                timestamp TEXT NOT NULL,

                previous_hash TEXT NOT NULL,

                block_hash TEXT NOT NULL,

                FOREIGN KEY
                (
                    election_id
                )
                REFERENCES elections(id)
                ON DELETE CASCADE,

                FOREIGN KEY
                (
                    vote_id
                )
                REFERENCES election_votes(id)
                ON DELETE SET NULL
            )
            """
        )

        # ====================================================
        # ELECTION INDEXES
        # ====================================================

        conn.execute(
            """
            CREATE INDEX IF NOT EXISTS
            idx_elections_status
            ON elections(status)
            """
        )

        conn.execute(
            """
            CREATE INDEX IF NOT EXISTS
            idx_election_candidates_election
            ON election_candidates(election_id)
            """
        )

        conn.execute(
            """
            CREATE INDEX IF NOT EXISTS
            idx_election_votes_election
            ON election_votes(election_id)
            """
        )

        conn.execute(
            """
            CREATE INDEX IF NOT EXISTS
            idx_election_votes_user
            ON election_votes(user_id)
            """
        )

        conn.execute(
            """
            CREATE INDEX IF NOT EXISTS
            idx_election_blockchain_election
            ON election_blockchain(election_id)
            """
        )

        # ====================================================
        # LEGACY ELECTION MIGRATION
        # ====================================================

        legacy_exists = conn.execute(
            """
            SELECT id
            FROM elections
            WHERE name = 'Legacy Election'
            LIMIT 1
            """
        ).fetchone()

        if not legacy_exists:

            old_settings = conn.execute(
                """
                SELECT *
                FROM voting_settings
                WHERE id = 1
                """
            ).fetchone()

            old_eligibility = conn.execute(
                """
                SELECT *
                FROM voting_eligibility
                WHERE id = 1
                """
            ).fetchone()

            legacy_start = (
                old_settings["start_datetime"]
                if old_settings
                else None
            )

            legacy_duration = int(
                (
                    old_settings["duration_seconds"]
                    if old_settings
                    else 0
                )
                or 0
            )

            legacy_scope = (
                old_eligibility["scope"]
                if old_eligibility
                else "all_india"
            )

            legacy_state = (
                old_eligibility["state"]
                if old_eligibility
                else None
            )

            legacy_district = (
                old_eligibility["district"]
                if old_eligibility
                else None
            )

            legacy_status = "draft"

            if (
                legacy_start
                and
                legacy_duration > 0
            ):

                try:

                    legacy_dt = (
                        datetime.fromisoformat(
                            legacy_start
                        )
                    )

                    legacy_end = (
                        legacy_dt
                        +
                        timedelta(
                            seconds=legacy_duration
                        )
                    )

                    if datetime.now() < legacy_dt:

                        legacy_status = "scheduled"

                    elif datetime.now() >= legacy_end:

                        legacy_status = "ended"

                    else:

                        legacy_status = "active"

                except Exception:

                    legacy_status = "draft"

            cursor = conn.execute(
                """
                INSERT INTO elections
                (
                    name,
                    description,
                    election_type,
                    scope,
                    state,
                    district,
                    start_datetime,
                    duration_seconds,
                    status,
                    archived,
                    created_at,
                    updated_at
                )
                VALUES
                (
                    ?,
                    ?,
                    ?,
                    ?,
                    ?,
                    ?,
                    ?,
                    ?,
                    ?,
                    0,
                    ?,
                    ?
                )
                """,
                (
                    "Legacy Election",
                    "Migrated from the original voting system.",
                    "general",
                    legacy_scope or "all_india",
                    legacy_state,
                    legacy_district,
                    legacy_start,
                    legacy_duration,
                    legacy_status,
                    datetime.now().isoformat(),
                    datetime.now().isoformat()
                )
            )

            legacy_election_id = (
                cursor.lastrowid
            )

            candidate_map = {}

            old_candidates = conn.execute(
                """
                SELECT *
                FROM candidates
                ORDER BY id
                """
            ).fetchall()

            for old_candidate in old_candidates:

                cursor = conn.execute(
                    """
                    INSERT INTO election_candidates
                    (
                        election_id,
                        name,
                        party,
                        party_symbol,
                        created_at
                    )
                    VALUES (?, ?, ?, ?, ?)
                    """,
                    (
                        legacy_election_id,
                        old_candidate["name"],
                        old_candidate["party"],
                        old_candidate["party_symbol"],
                        datetime.now().isoformat()
                    )
                )

                candidate_map[
                    old_candidate["id"]
                ] = cursor.lastrowid

            voted_users = conn.execute(
                """
                SELECT *
                FROM users
                WHERE has_voted = 1
                AND voted_candidate_id IS NOT NULL
                """
            ).fetchall()

            for old_user in voted_users:

                new_candidate_id = (
                    candidate_map.get(
                        old_user["voted_candidate_id"]
                    )
                )

                if not new_candidate_id:
                    continue

                vote_timestamp = (
                    old_user["registration_date"]
                    or
                    datetime.now().isoformat()
                )

                voter_hash = hashlib.sha256(
                    str(
                        old_user["id"]
                    ).encode("utf-8")
                ).hexdigest()

                try:

                    cursor = conn.execute(
                        """
                        INSERT OR IGNORE INTO election_votes
                        (
                            election_id,
                            user_id,
                            candidate_id,
                            timestamp,
                            voter_hash
                        )
                        VALUES (?, ?, ?, ?, ?)
                        """,
                        (
                            legacy_election_id,
                            old_user["id"],
                            new_candidate_id,
                            vote_timestamp,
                            voter_hash
                        )
                    )

                    vote_id = cursor.lastrowid

                    if vote_id:

                        existing_block = conn.execute(
                            """
                            SELECT id
                            FROM election_blockchain
                            WHERE vote_id = ?
                            """,
                            (
                                vote_id,
                            )
                        ).fetchone()

                        if not existing_block:

                            previous = conn.execute(
                                """
                                SELECT block_hash
                                FROM election_blockchain
                                WHERE election_id = ?
                                ORDER BY id DESC
                                LIMIT 1
                                """,
                                (
                                    legacy_election_id,
                                )
                            ).fetchone()

                            previous_hash = (
                                previous["block_hash"]
                                if previous
                                else
                                "0" * 64
                            )

                            row = conn.execute(
                                """
                                SELECT
                                    COALESCE(
                                        MAX(id),
                                        0
                                    ) + 1 AS next_id
                                FROM election_blockchain
                                """
                            ).fetchone()

                            block_id = row["next_id"]

                            candidate_name = conn.execute(
                                """
                                SELECT name
                                FROM election_candidates
                                WHERE id = ?
                                """,
                                (
                                    new_candidate_id,
                                )
                            ).fetchone()["name"]

                            block_hash = (
                                calculate_election_block_hash(
                                    block_id,
                                    voter_hash,
                                    candidate_name,
                                    vote_timestamp,
                                    previous_hash
                                )
                            )

                            conn.execute(
                                """
                                INSERT INTO election_blockchain
                                (
                                    election_id,
                                    vote_id,
                                    voter_hash,
                                    candidate_name,
                                    timestamp,
                                    previous_hash,
                                    block_hash
                                )
                                VALUES (?, ?, ?, ?, ?, ?, ?)
                                """,
                                (
                                    legacy_election_id,
                                    vote_id,
                                    voter_hash,
                                    candidate_name,
                                    vote_timestamp,
                                    previous_hash,
                                    block_hash
                                )
                            )

                except sqlite3.Error as migration_error:

                    print(
                        "Legacy vote migration warning:",
                        migration_error
                    )

        conn.commit()

    except Exception:

        conn.rollback()
        raise

    finally:

        conn.close()


# ============================================================
# TEMPLATE CONTEXT
# ============================================================

@app.context_processor
def inject_global_context():

    return {

        "indian_states":
            INDIAN_STATES,

        "india_districts":
            INDIA_DISTRICTS,

        "country":
            COUNTRY
    }


# ============================================================
# AGE HELPERS
# ============================================================

def calculate_age(
    dob_string
):

    try:

        birth_date = datetime.strptime(
            dob_string,
            "%Y-%m-%d"
        ).date()

        today = date.today()

        age = (
            today.year
            -
            birth_date.year
            -
            (
                (
                    today.month,
                    today.day
                )
                <
                (
                    birth_date.month,
                    birth_date.day
                )
            )
        )

        return age

    except Exception:

        return -1


def is_18_or_above(
    dob_string
):

    return (
        calculate_age(dob_string)
        >=
        18
    )


# ============================================================
# AADHAAR
# ============================================================

def validate_aadhaar(
    aadhaar
):

    cleaned = re.sub(
        r"\s+",
        "",
        aadhaar or ""
    )

    return bool(
        re.fullmatch(
            r"\d{12}",
            cleaned
        )
    )


# ============================================================
# PHOTO DECODING
# ============================================================

def decode_base64_image(
    photo_data
):

    if not photo_data:

        return None

    try:

        if "," in photo_data:

            photo_data = (
                photo_data.split(
                    ",",
                    1
                )[1]
            )

        image_bytes = base64.b64decode(
            photo_data,
            validate=True
        )

        if not image_bytes:

            return None

        if len(image_bytes) > (
            5 * 1024 * 1024
        ):

            return None

        return image_bytes

    except Exception:

        return None


# ============================================================
# PHOTO VALIDATION
# ============================================================

def validate_photo_with_opencv(
    image_bytes
):

    if not OPENCV_AVAILABLE:

        return (
            False,
            "Camera validation requires OpenCV. Please install opencv-python."
        )

    try:

        array = np.frombuffer(
            image_bytes,
            dtype=np.uint8
        )

        image = cv2.imdecode(
            array,
            cv2.IMREAD_COLOR
        )

        if image is None:

            return (
                False,
                "Invalid image."
            )

        height, width = image.shape[:2]

        if (
            width < 300
            or
            height < 300
        ):

            return (
                False,
                "Photo resolution must be at least 300x300."
            )

        gray = cv2.cvtColor(
            image,
            cv2.COLOR_BGR2GRAY
        )

        brightness = float(
            gray.mean()
        )

        if (
            brightness < 35
            or
            brightness > 235
        ):

            return (
                False,
                "Please capture a clearer photo with proper lighting."
            )

        cascade_path = os.path.join(
            cv2.data.haarcascades,
            "haarcascade_frontalface_default.xml"
        )

        face_cascade = cv2.CascadeClassifier(
            cascade_path
        )

        faces = face_cascade.detectMultiScale(
            gray,
            scaleFactor=1.1,
            minNeighbors=5,
            minSize=(80, 80)
        )

        if len(faces) == 0:

            return (
                False,
                "No face detected. Please capture your face clearly."
            )

        if len(faces) > 1:

            return (
                False,
                "Multiple faces detected. Please capture only one person."
            )

        return (
            True,
            "Photo validated successfully."
        )

    except Exception as e:

        print(
            "Photo validation error:",
            e
        )

        return (
            False,
            "Unable to validate photo."
        )


# ============================================================
# SAVE CAMERA PHOTO
# ============================================================

def save_camera_photo(
    image_bytes,
    user_id
):

    timestamp = (
        datetime.now()
        .strftime("%Y%m%d%H%M%S%f")
    )

    filename = (
        f"voter_{user_id}_{timestamp}.jpg"
    )

    filepath = os.path.join(
        UPLOAD_FOLDER,
        secure_filename(filename)
    )

    if OPENCV_AVAILABLE:

        try:

            array = np.frombuffer(
                image_bytes,
                dtype=np.uint8
            )

            image = cv2.imdecode(
                array,
                cv2.IMREAD_COLOR
            )

            if image is not None:

                cv2.imwrite(
                    filepath,
                    image
                )

                return filename

        except Exception as e:

            print(
                "OpenCV photo save error:",
                e
            )

    with open(
        filepath,
        "wb"
    ) as file:

        file.write(
            image_bytes
        )

    return filename


# ============================================================
# NORMALIZE SELECTION
# ============================================================

def normalize_selection(
    value
):

    return (
        str(value or "")
        .strip()
        .lower()
    )


# ============================================================
# LOCATION ELIGIBILITY
# ============================================================

def is_location_allowed(
    user,
    eligibility=None
):

    if not user:

        return False

    if eligibility is None:

        return True

    scope = normalize_selection(
        eligibility["scope"]
    )

    user_state = normalize_selection(
        user["state"]
    )

    user_district = normalize_selection(
        user["district"]
    )

    selected_state = normalize_selection(
        eligibility["state"]
    )

    selected_district = normalize_selection(
        eligibility["district"]
    )

    # ========================================================
    # ALL INDIA
    # ========================================================

    if scope in (
        "",
        "all",
        "all_india",
        "india"
    ):

        return True

    # ========================================================
    # STATE
    # ========================================================

    if scope == "state":

        if (
            not selected_state
            or
            selected_state in (
                "all",
                "all states"
            )
        ):

            return True

        return (
            user_state
            ==
            selected_state
        )

    # ========================================================
    # DISTRICT
    # ========================================================

    if scope == "district":

        if (
            selected_state
            and
            selected_state not in (
                "all",
                "all states"
            )
            and
            user_state != selected_state
        ):

            return False

        if (
            not selected_district
            or
            selected_district in (
                "all",
                "all districts"
            )
        ):

            return True

        return (
            user_district
            ==
            selected_district
        )

    return False


# ============================================================
# GET VOTING SETTINGS
# ============================================================

def get_voting_settings():

    conn = get_db()

    try:

        return conn.execute(
            """
            SELECT *
            FROM voting_settings
            WHERE id = 1
            """
        ).fetchone()

    finally:

        conn.close()


# ============================================================
# LEGACY VOTING STATUS
# ============================================================

def voting_status():

    settings = get_voting_settings()

    if not settings:

        return "not_started"

    start_value = (
        settings["start_datetime"]
    )

    duration = int(
        settings["duration_seconds"]
        or 0
    )

    if (
        not start_value
        or
        duration <= 0
    ):

        return "not_started"

    try:

        start = datetime.fromisoformat(
            start_value
        )

    except (
        ValueError,
        TypeError
    ):

        return "not_started"

    now = datetime.now()

    end = (
        start
        +
        timedelta(
            seconds=duration
        )
    )

    if now < start:

        return "not_started"

    if now >= end:

        return "ended"

    return "active"


# ============================================================
# LEGACY REMAINING TIME
# ============================================================

def voting_remaining_seconds():

    settings = get_voting_settings()

    if not settings:

        return 0

    try:

        if not settings["start_datetime"]:

            return 0

        start = datetime.fromisoformat(
            settings["start_datetime"]
        )

        duration = int(
            settings["duration_seconds"]
            or 0
        )

        if duration <= 0:

            return 0

        end = (
            start
            +
            timedelta(
                seconds=duration
            )
        )

        remaining = (
            end
            -
            datetime.now()
        ).total_seconds()

        return max(
            0,
            int(remaining)
        )

    except Exception:

        return 0


# ============================================================
# GET ELECTION
# ============================================================

def get_election(
    election_id
):

    conn = get_db()

    try:

        return conn.execute(
            """
            SELECT *
            FROM elections
            WHERE id = ?
            """,
            (
                election_id,
            )
        ).fetchone()

    finally:

        conn.close()


# ============================================================
# ELECTION STATUS
# ============================================================

def election_status(
    election
):

    if not election:

        return "not_found"

    if int(
        election["archived"] or 0
    ) == 1:

        return "archived"

    start_value = (
        election["start_datetime"]
    )

    duration = int(
        election["duration_seconds"]
        or 0
    )

    if (
        not start_value
        or
        duration <= 0
    ):

        return "not_started"

    try:

        start = datetime.fromisoformat(
            start_value
        )

    except (
        ValueError,
        TypeError
    ):

        return "not_started"

    now = datetime.now()

    end = (
        start
        +
        timedelta(
            seconds=duration
        )
    )

    if now < start:

        return "not_started"

    if now >= end:

        return "ended"

    return "active"


# ============================================================
# ELECTION REMAINING TIME
# ============================================================

def election_remaining_seconds(
    election
):

    if not election:

        return 0

    try:

        start_value = (
            election["start_datetime"]
        )

        duration = int(
            election["duration_seconds"]
            or 0
        )

        if (
            not start_value
            or
            duration <= 0
        ):

            return 0

        start = datetime.fromisoformat(
            start_value
        )

        end = (
            start
            +
            timedelta(
                seconds=duration
            )
        )

        return max(
            0,
            int(
                (
                    end
                    -
                    datetime.now()
                ).total_seconds()
            )
        )

    except Exception:

        return 0


# ============================================================
# BLOCKCHAIN HASH
# ============================================================

def calculate_block_hash(
    block_id,
    voter_hash,
    candidate_name,
    timestamp,
    previous_hash
):

    data = (
        f"{block_id}|"
        f"{voter_hash}|"
        f"{candidate_name}|"
        f"{timestamp}|"
        f"{previous_hash}"
    )

    return hashlib.sha256(
        data.encode("utf-8")
    ).hexdigest()


# ============================================================
# ELECTION BLOCKCHAIN HASH
# ============================================================

def calculate_election_block_hash(
    block_id,
    voter_hash,
    candidate_name,
    timestamp,
    previous_hash
):

    return calculate_block_hash(
        block_id,
        voter_hash,
        candidate_name,
        timestamp,
        previous_hash
    )


# ============================================================
# ADD LEGACY BLOCKCHAIN
# ============================================================

def add_vote_to_blockchain(
    conn,
    user_id,
    candidate_name
):

    previous = conn.execute(
        """
        SELECT block_hash
        FROM blockchain
        ORDER BY id DESC
        LIMIT 1
        """
    ).fetchone()

    previous_hash = (
        previous["block_hash"]
        if previous
        else
        "0" * 64
    )

    timestamp = (
        datetime.now().isoformat()
    )

    voter_hash = hashlib.sha256(
        str(user_id).encode(
            "utf-8"
        )
    ).hexdigest()

    row = conn.execute(
        """
        SELECT
            COALESCE(
                MAX(id),
                0
            ) + 1 AS next_id
        FROM blockchain
        """
    ).fetchone()

    block_id = row["next_id"]

    block_hash = calculate_block_hash(
        block_id,
        voter_hash,
        candidate_name,
        timestamp,
        previous_hash
    )

    conn.execute(
        """
        INSERT INTO blockchain
        (
            voter_hash,
            candidate_name,
            timestamp,
            previous_hash,
            block_hash
        )
        VALUES (?, ?, ?, ?, ?)
        """,
        (
            voter_hash,
            candidate_name,
            timestamp,
            previous_hash,
            block_hash
        )
    )


# ============================================================
# ADD ELECTION BLOCKCHAIN
# ============================================================

def add_election_vote_to_blockchain(
    conn,
    election_id,
    vote_id,
    user_id,
    candidate_name,
    timestamp,
    voter_hash
):

    previous = conn.execute(
        """
        SELECT block_hash
        FROM election_blockchain
        WHERE election_id = ?
        ORDER BY id DESC
        LIMIT 1
        """,
        (
            election_id,
        )
    ).fetchone()

    previous_hash = (
        previous["block_hash"]
        if previous
        else
        "0" * 64
    )

    row = conn.execute(
        """
        SELECT
            COALESCE(
                MAX(id),
                0
            ) + 1 AS next_id
        FROM election_blockchain
        """
    ).fetchone()

    block_id = row["next_id"]

    block_hash = (
        calculate_election_block_hash(
            block_id,
            voter_hash,
            candidate_name,
            timestamp,
            previous_hash
        )
    )

    conn.execute(
        """
        INSERT INTO election_blockchain
        (
            election_id,
            vote_id,
            voter_hash,
            candidate_name,
            timestamp,
            previous_hash,
            block_hash
        )
        VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (
            election_id,
            vote_id,
            voter_hash,
            candidate_name,
            timestamp,
            previous_hash,
            block_hash
        )
    )


# ============================================================
# VERIFY LEGACY BLOCKCHAIN
# ============================================================

def verify_blockchain():

    conn = get_db()

    try:

        blocks = conn.execute(
            """
            SELECT *
            FROM blockchain
            ORDER BY id ASC
            """
        ).fetchall()

        previous_hash = (
            "0" * 64
        )

        for block in blocks:

            expected_hash = (
                calculate_block_hash(
                    block["id"],
                    block["voter_hash"],
                    block["candidate_name"],
                    block["timestamp"],
                    block["previous_hash"]
                )
            )

            if (
                block["previous_hash"]
                !=
                previous_hash
            ):

                return (
                    False,
                    f"Invalid previous hash at block {block['id']}."
                )

            if (
                block["block_hash"]
                !=
                expected_hash
            ):

                return (
                    False,
                    f"Invalid block hash at block {block['id']}."
                )

            previous_hash = (
                block["block_hash"]
            )

        return (
            True,
            "Blockchain is valid."
        )

    finally:

        conn.close()


# ============================================================
# VERIFY ELECTION BLOCKCHAIN
# ============================================================

def verify_election_blockchain(
    election_id
):

    conn = get_db()

    try:

        blocks = conn.execute(
            """
            SELECT *
            FROM election_blockchain
            WHERE election_id = ?
            ORDER BY id ASC
            """,
            (
                election_id,
            )
        ).fetchall()

        previous_hash = (
            "0" * 64
        )

        for block in blocks:

            expected_hash = (
                calculate_election_block_hash(
                    block["id"],
                    block["voter_hash"],
                    block["candidate_name"],
                    block["timestamp"],
                    block["previous_hash"]
                )
            )

            if (
                block["previous_hash"]
                !=
                previous_hash
            ):

                return (
                    False,
                    f"Invalid previous hash at block {block['id']}."
                )

            if (
                block["block_hash"]
                !=
                expected_hash
            ):

                return (
                    False,
                    f"Invalid block hash at block {block['id']}."
                )

            previous_hash = (
                block["block_hash"]
            )

        return (
            True,
            "Election blockchain is valid."
        )

    finally:

        conn.close()


# ============================================================
# EMAIL
# ============================================================

def send_email(
    recipient,
    subject,
    body
):

    smtp_host = os.environ.get(
        "SMTP_HOST"
    )

    smtp_port = os.environ.get(
        "SMTP_PORT",
        "587"
    )

    smtp_username = os.environ.get(
        "SMTP_USERNAME"
    )

    smtp_password = os.environ.get(
        "SMTP_PASSWORD"
    )

    if not all([
        smtp_host,
        smtp_username,
        smtp_password
    ]):

        print(
            "\nSMTP is not configured."
        )

        print(
            "Email recipient:",
            recipient
        )

        print(
            "Email subject:",
            subject
        )

        print(
            body
        )

        return False

    try:

        message = EmailMessage()

        message["From"] = (
            smtp_username
        )

        message["To"] = (
            recipient
        )

        message["Subject"] = (
            subject
        )

        message.set_content(
            body
        )

        with smtplib.SMTP(
            smtp_host,
            int(smtp_port),
            timeout=20
        ) as server:

            server.starttls()

            server.login(
                smtp_username,
                smtp_password
            )

            server.send_message(
                message
            )

        return True

    except Exception as e:

        print(
            "Email error:",
            e
        )

        return False


# ============================================================
# HOME
# ============================================================

@app.route("/")
def index():

    return render_template(
        "index.html"
    )


# ============================================================
# LIVE DUPLICATE CHECK (AJAX)
# ============================================================

@app.route("/check-registration-field", methods=["POST"])
def check_registration_field():
    """Check Aadhaar, mobile, or email while the user is filling the form."""
    data = request.get_json(silent=True) or {}
    field = (data.get("field") or "").strip().lower()
    raw_value = (data.get("value") or "").strip()

    if field not in {"aadhaar", "mobile", "email"}:
        return jsonify({"valid": False, "duplicate": False, "message": "Invalid field."}), 400

    if field == "aadhaar":
        value = re.sub(r"\D", "", raw_value)
        # Wait until all 12 digits have been entered.
        if len(value) != 12:
            return jsonify({"valid": False, "duplicate": False, "message": ""})
        value_hash = hashlib.sha256(value.encode("utf-8")).hexdigest()
        sql = """SELECT 1 FROM users WHERE
                 REPLACE(REPLACE(REPLACE(TRIM(COALESCE(aadhaar, '')), ' ', ''), '-', ''), '.', '') = ?
                 OR aadhaar_hash = ? LIMIT 1"""
        params = (value, value_hash)
        message = "This Aadhaar number is already registered."
    elif field == "mobile":
        value = re.sub(r"\D", "", raw_value)
        # Wait until a complete 10-digit mobile number is entered.
        if not re.fullmatch(r"[6-9]\d{9}", value):
            return jsonify({"valid": False, "duplicate": False, "message": ""})
        sql = """SELECT 1 FROM users WHERE
                 REPLACE(REPLACE(REPLACE(TRIM(COALESCE(mobile, '')), ' ', ''), '-', ''), '.', '') = ?
                 LIMIT 1"""
        params = (value,)
        message = "This mobile number is already registered."
    else:
        value = raw_value.lower()
        # Check after a plausible complete email has been typed.
        if not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", value):
            return jsonify({"valid": False, "duplicate": False, "message": ""})
        sql = "SELECT 1 FROM users WHERE LOWER(TRIM(COALESCE(email, ''))) = ? LIMIT 1"
        params = (value,)
        message = "This email address is already registered."

    conn = get_db()
    try:
        duplicate = conn.execute(sql, params).fetchone()
        return jsonify({
            "valid": True,
            "duplicate": bool(duplicate),
            "message": message if duplicate else ""
        })
    finally:
        conn.close()


# ============================================================
# REGISTER
# ============================================================

@app.route(
    "/register",
    methods=[
        "GET",
        "POST"
    ]
)
def register():

    if request.method == "GET":

        return render_template(
            "register.html"
        )

    name = request.form.get(
        "name",
        ""
    ).strip()

    father_name = request.form.get(
        "father_name",
        ""
    ).strip()

    dob = request.form.get(
        "dob",
        ""
    ).strip()

    aadhaar = re.sub(
        r"\D",
        "",
        request.form.get(
            "aadhaar",
            ""
        )
    )

    mobile = re.sub(
        r"\D",
        "",
        request.form.get(
            "mobile",
            ""
        )
    )

    email = request.form.get(
        "email",
        ""
    ).strip().lower()

    password = request.form.get(
        "password",
        ""
    )

    confirm_password = request.form.get(
        "confirm_password",
        ""
    )

    address = request.form.get(
        "address",
        ""
    ).strip()

    state = request.form.get(
        "state",
        ""
    ).strip()

    district = request.form.get(
        "district",
        ""
    ).strip()

    declaration = request.form.get(
        "declaration"
    )

    photo_data = request.form.get(
        "photo_data",
        ""
    )

    if not all([
        name,
        father_name,
        dob,
        aadhaar,
        mobile,
        email,
        password,
        confirm_password,
        address,
        state,
        district,
        declaration,
        photo_data
    ]):

        flash(
            "Please fill all required fields.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    if len(name) < 2:

        flash(
            "Please enter a valid name.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    try:

        birth_date = datetime.strptime(
            dob,
            "%Y-%m-%d"
        ).date()

        if birth_date > date.today():

            flash(
                "Date of birth cannot be in the future.",
                "danger"
            )

            return redirect(
                url_for("register")
            )

    except ValueError:

        flash(
            "Invalid date of birth.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    if not is_18_or_above(dob):

        flash(
            "You must be 18 years or older.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    if not validate_aadhaar(
        aadhaar
    ):

        flash(
            "Aadhaar must contain exactly 12 digits.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    if not re.fullmatch(
        r"[6-9]\d{9}",
        mobile
    ):

        flash(
            "Please enter a valid 10-digit mobile number.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    if not re.fullmatch(
        r"[^@\s]+@[^@\s]+\.[^@\s]+",
        email
    ):

        flash(
            "Please enter a valid email address.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    if len(password) < 6:

        flash(
            "Password must contain at least 6 characters.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    if password != confirm_password:

        flash(
            "Passwords do not match.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    if state not in INDIAN_STATES:

        flash(
            "Please select a valid state/UT.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    if (
        state not in INDIA_DISTRICTS
        or
        (
            INDIA_DISTRICTS[state]
            and
            district not in INDIA_DISTRICTS[state]
        )
    ):

        flash(
            "Please select a valid district.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    photo_bytes = decode_base64_image(
        photo_data
    )

    if not photo_bytes:

        flash(
            "Unable to read the captured photo.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    photo_valid, photo_message = (
        validate_photo_with_opencv(
            photo_bytes
        )
    )

    if not photo_valid:

        flash(
            photo_message,
            "danger"
        )

        return redirect(
            url_for("register")
        )

    conn = get_db()

    try:

        # Check all three identifiers before inserting the voter.
        # Normalize Aadhaar/mobile to digits above and email to lowercase above.
        duplicate = conn.execute(
            """
            SELECT id
            FROM users
            WHERE
                REPLACE(REPLACE(REPLACE(TRIM(COALESCE(aadhaar, '')), ' ', ''), '-', ''), '.', '') = ?
                OR
                REPLACE(REPLACE(REPLACE(TRIM(COALESCE(mobile, '')), ' ', ''), '-', ''), '.', '') = ?
                OR
                LOWER(TRIM(COALESCE(email, ''))) = ?
            LIMIT 1
            """,
            (
                aadhaar,
                mobile,
                email
            )
        ).fetchone()

        if duplicate:

            flash(
                "Registration blocked: this Aadhaar number, mobile number, or email address is already registered. Please use unique details.",
                "danger"
            )

            return redirect(
                url_for("register")
            )

        password_hash = (
            generate_password_hash(
                password
            )
        )

        aadhaar_hash = hashlib.sha256(
            aadhaar.encode(
                "utf-8"
            )
        ).hexdigest()

        registration_date = (
            datetime.now().isoformat()
        )

        cursor = conn.execute(
            """
            INSERT INTO users
            (
                name,
                father_name,
                dob,
                aadhaar,
                aadhaar_hash,
                mobile,
                email,
                password,
                address,
                state,
                district,
                country,
                photo,
                eligible,
                has_voted,
                voted_candidate_id,
                registration_date
            )
            VALUES
            (
                ?, ?, ?, ?, ?, ?,
                ?, ?, ?, ?, ?, ?,
                ?, 1, 0, NULL, ?
            )
            """,
            (
                name,
                father_name,
                dob,
                aadhaar,
                aadhaar_hash,
                mobile,
                email,
                password_hash,
                address,
                state,
                district,
                COUNTRY,
                None,
                registration_date
            )
        )

        user_id = (
            cursor.lastrowid
        )

        filename = save_camera_photo(
            photo_bytes,
            user_id
        )

        conn.execute(
            """
            UPDATE users
            SET photo = ?
            WHERE id = ?
            """,
            (
                filename,
                user_id
            )
        )

        conn.commit()

        flash(
            "Registration successful. You can now login.",
            "success"
        )

        return redirect(
            url_for("login")
        )

    except sqlite3.IntegrityError:

        conn.rollback()

        flash(
            "Registration blocked: this Aadhaar number, mobile number, or email address is already registered. Please use unique details.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    except Exception as e:

        conn.rollback()

        print(
            "Registration error:",
            e
        )

        flash(
            "Registration failed. Please try again.",
            "danger"
        )

        return redirect(
            url_for("register")
        )

    finally:

        conn.close()


# ============================================================
# LOGIN
# ============================================================

@app.route(
    "/login",
    methods=[
        "GET",
        "POST"
    ]
)
def login():

    if request.method == "GET":

        return render_template(
            "login.html"
        )

    email = request.form.get(
        "email",
        ""
    ).strip().lower()

    password = request.form.get(
        "password",
        ""
    )

    conn = get_db()

    try:

        user = conn.execute(
            """
            SELECT *
            FROM users
            WHERE LOWER(email) = ?
            """,
            (
                email,
            )
        ).fetchone()

    finally:

        conn.close()

    if not user:

        flash(
            "Invalid email or password.",
            "danger"
        )

        return redirect(
            url_for("login")
        )

    if not user["password"]:

        flash(
            "This account does not have a valid password.",
            "danger"
        )

        return redirect(
            url_for("login")
        )

    if not check_password_hash(
        user["password"],
        password
    ):

        flash(
            "Invalid email or password.",
            "danger"
        )

        return redirect(
            url_for("login")
        )

    session.clear()

    session["user_id"] = (
        user["id"]
    )

    session["user_email"] = (
        user["email"]
    )

    return redirect(
        url_for("dashboard")
    )


# ============================================================
# USER DASHBOARD
# ============================================================

@app.route("/dashboard")
def dashboard():
    """Show the logged-in voter's dashboard and recover a partial session safely."""

    # If user_id is missing but the user's email remains in the session,
    # recover the voter ID from the existing users table.
    if "user_id" not in session:
        saved_email = session.get("user_email")

        if saved_email:
            conn = get_db()
            try:
                recovered_user = conn.execute(
                    """
                    SELECT id, email
                    FROM users
                    WHERE LOWER(email) = LOWER(?)
                    LIMIT 1
                    """,
                    (saved_email,)
                ).fetchone()
            finally:
                conn.close()

            if recovered_user:
                session["user_id"] = recovered_user["id"]
                session["user_email"] = recovered_user["email"]
            else:
                session.clear()
                return redirect(url_for("login"))
        else:
            # Keep admin sessions directed to the admin dashboard.
            if "admin_id" in session:
                return redirect(url_for("admin_dashboard"))
            return redirect(url_for("login"))

    conn = get_db()

    try:
        user = conn.execute(
            """
            SELECT *
            FROM users
            WHERE id = ?
            """,
            (session.get("user_id"),)
        ).fetchone()

        # Validate the session user before accessing user fields.
        if not user:
            session.clear()
            return redirect(url_for("login"))

        elections = conn.execute(
            """
            SELECT *
            FROM elections
            WHERE archived = 0
            ORDER BY id DESC
            """
        ).fetchall()

        election_data = []

        for election in elections:
            allowed = (
                bool(user["eligible"])
                and is_location_allowed(user, election)
            )

            status = election_status(election)

            vote = conn.execute(
                """
                SELECT id
                FROM election_votes
                WHERE election_id = ?
                  AND user_id = ?
                """,
                (election["id"], user["id"])
            ).fetchone()

            candidate_count = conn.execute(
                """
                SELECT COUNT(*)
                FROM election_candidates
                WHERE election_id = ?
                """,
                (election["id"],)
            ).fetchone()[0]

            vote_count = conn.execute(
                """
                SELECT COUNT(*)
                FROM election_votes
                WHERE election_id = ?
                """,
                (election["id"],)
            ).fetchone()[0]

            election_data.append({
                "election": election,
                "status": status,
                "allowed": allowed,
                "has_voted": bool(vote),
                "remaining_seconds": election_remaining_seconds(election),
                "candidate_count": candidate_count,
                "vote_count": vote_count
            })

    finally:
        conn.close()

    return render_template(
        "dashboard.html",
        user=user,
        location_allowed=True,
        voting_state=voting_status(),
        elections=election_data
    )

# ============================================================
# VOTE PAGE
# ============================================================

@app.route(
    "/vote/<int:election_id>"
)
def vote(
    election_id
):

    if "user_id" not in session:

        return redirect(
            url_for("login")
        )

    election = get_election(
        election_id
    )

    if not election:

        flash(
            "Election not found.",
            "danger"
        )

        return redirect(
            url_for("dashboard")
        )

    status = election_status(
        election
    )

    if status == "not_started":

        return render_template(
            "voting_not_started.html",
            election=election
        )

    if status == "ended":

        return redirect(
            url_for(
                "election_results",
                election_id=election_id
            )
        )

    if status == "archived":

        flash(
            "This election has been archived.",
            "warning"
        )

        return redirect(
            url_for("dashboard")
        )

    conn = get_db()

    try:

        user = conn.execute(
            """
            SELECT *
            FROM users
            WHERE id = ?
            """,
            (
                session["user_id"],
            )
        ).fetchone()

        candidates = conn.execute(
            """
            SELECT *
            FROM election_candidates
            WHERE election_id = ?
            ORDER BY id
            """,
            (
                election_id,
            )
        ).fetchall()

        existing_vote = conn.execute(
            """
            SELECT *
            FROM election_votes
            WHERE election_id = ?
            AND user_id = ?
            """,
            (
                election_id,
                session["user_id"]
            )
        ).fetchone()

    finally:

        conn.close()

    if not user:

        session.clear()

        return redirect(
            url_for("login")
        )

    if not user["eligible"]:

        return redirect(
            url_for("not_eligible")
        )

    if not is_location_allowed(
        user,
        election
    ):

        return redirect(
            url_for("not_eligible")
        )

    if existing_vote:

        return redirect(
            url_for(
                "already_voted",
                election_id=election_id
            )
        )

    if not candidates:

        flash(
            "No candidates have been added to this election yet.",
            "warning"
        )

        return redirect(
            url_for("dashboard")
        )

    return render_template(
        "vote.html",
        user=user,
        election=election,
        candidates=candidates,
        remaining_seconds=(
            election_remaining_seconds(
                election
            )
        )
    )


# ============================================================
# SUBMIT VOTE
# ============================================================

@app.route(
    "/submit_vote/<int:election_id>",
    methods=["POST"]
)
def submit_vote(
    election_id
):

    if "user_id" not in session:

        return redirect(
            url_for("login")
        )

    candidate_id = request.form.get(
        "candidate_id",
        ""
    ).strip()

    try:

        candidate_id = int(
            candidate_id
        )

    except (
        ValueError,
        TypeError
    ):

        flash(
            "Please select a valid candidate.",
            "danger"
        )

        return redirect(
            url_for(
                "vote",
                election_id=election_id
            )
        )

    conn = get_db()

    try:

        conn.execute(
            "BEGIN IMMEDIATE"
        )

        election = conn.execute(
            """
            SELECT *
            FROM elections
            WHERE id = ?
            AND archived = 0
            """,
            (
                election_id,
            )
        ).fetchone()

        if not election:

            conn.rollback()

            flash(
                "Election not found.",
                "danger"
            )

            return redirect(
                url_for("dashboard")
            )

        status = election_status(
            election
        )
        print("DEBUG ELECTION ID:", election_id)
        print("DEBUG ELECTION STATUS:", status)
        print("DEBUG CANDIDATE ID:", candidate_id)
        print("DEBUG USER ID:", session.get("user_id"))

        if status != "active":

            conn.rollback()

            if status == "ended":

                return redirect(
                    url_for(
                        "election_results",
                        election_id=election_id
                    )
                )

            return render_template(
                "voting_not_started.html",
                election=election
            )

        user = conn.execute(
            """
            SELECT *
            FROM users
            WHERE id = ?
            """,
            (
                session["user_id"],
            )
        ).fetchone()

        if not user:

            conn.rollback()

            session.clear()

            return redirect(
                url_for("login")
            )

        if not user["eligible"]:

            conn.rollback()

            return redirect(
                url_for("not_eligible")
            )

        if not is_location_allowed(
            user,
            election
        ):

            conn.rollback()

            return redirect(
                url_for("not_eligible")
            )

        existing_vote = conn.execute(
            """
            SELECT id
            FROM election_votes
            WHERE election_id = ?
            AND user_id = ?
            """,
            (
                election_id,
                user["id"]
            )
        ).fetchone()

        if existing_vote:

            conn.rollback()

            return redirect(
                url_for(
                    "already_voted",
                    election_id=election_id
                )
            )

        candidate = conn.execute(
            """
            SELECT *
            FROM election_candidates
            WHERE id = ?
            AND election_id = ?
            """,
            (
                candidate_id,
                election_id
            )
        ).fetchone()

        if not candidate:

            conn.rollback()

            flash(
                "Selected candidate does not exist.",
                "danger"
            )

            return redirect(
                url_for(
                    "vote",
                    election_id=election_id
                )
            )

        voter_hash = hashlib.sha256(
            str(
                user["id"]
            ).encode("utf-8")
        ).hexdigest()

        timestamp = (
            datetime.now().isoformat()
        )

        cursor = conn.execute(
            """
            INSERT INTO election_votes
            (
                election_id,
                user_id,
                candidate_id,
                timestamp,
                voter_hash
            )
            VALUES (?, ?, ?, ?, ?)
            """,
            (
                election_id,
                user["id"],
                candidate_id,
                timestamp,
                voter_hash
            )
        )

        vote_id = (
            cursor.lastrowid
        )

        add_election_vote_to_blockchain(
            conn,
            election_id,
            vote_id,
            user["id"],
            candidate["name"],
            timestamp,
            voter_hash
        )

        # ----------------------------------------------------
        # LEGACY FIELDS
        #
        # These are kept only for old templates/data.
        # They are NOT used to prevent another election vote.
        # ----------------------------------------------------

        # Update only the legacy has_voted flag.
        # Do NOT store election_candidates.id in users.voted_candidate_id:
        # that legacy column may reference the separate legacy candidates table,
        # causing FOREIGN KEY constraint failed and rolling back the real vote.
        conn.execute(
            """
            UPDATE users
            SET has_voted = 1
            WHERE id = ?
            """,
            (user["id"],)
        )

        conn.commit()

        return redirect(
            url_for(
                "thank_you",
                election_id=election_id
            )
        )

    except sqlite3.IntegrityError as e:

        # Do not treat every SQLite integrity error as a duplicate vote.
        # A foreign-key/schema/NOT NULL failure can also raise IntegrityError.
        print("VOTE INTEGRITY ERROR:", repr(e))
        conn.rollback()

        # Only redirect to the already-voted page when a vote really exists.
        try:
            saved_vote = conn.execute(
                "SELECT id FROM election_votes WHERE election_id = ? AND user_id = ?",
                (election_id, session.get("user_id"))
            ).fetchone()
        except sqlite3.Error as check_error:
            print("VOTE CHECK ERROR AFTER ROLLBACK:", repr(check_error))
            saved_vote = None

        if saved_vote:
            flash(
                "A vote is already recorded for your account in this election.",
                "warning"
            )
            return redirect(
                url_for("already_voted", election_id=election_id)
            )

        flash(
            "The vote was not saved because of a database constraint error. Check the Flask terminal for VOTE INTEGRITY ERROR.",
            "danger"
        )
        return redirect(
            url_for("vote", election_id=election_id)
        )

    except Exception as e:

        conn.rollback()

        print(
            "Vote submission error:",
            e
        )

        flash(
            "Vote could not be submitted. Please try again.",
            "danger"
        )

        return redirect(
            url_for(
                "vote",
                election_id=election_id
            )
        )

    finally:

        conn.close()


# ============================================================
# THANK YOU
# ============================================================

@app.route(
    "/thank_you/<int:election_id>"
)
def thank_you(
    election_id
):

    if "user_id" not in session:

        return redirect(
            url_for("login")
        )

    election = get_election(
        election_id
    )

    if not election:

        return redirect(
            url_for("dashboard")
        )

    conn = get_db()

    try:

        user = conn.execute(
            """
            SELECT *
            FROM users
            WHERE id = ?
            """,
            (
                session["user_id"],
            )
        ).fetchone()

    finally:

        conn.close()

    if not user:

        return redirect(
            url_for("login")
        )

    return render_template(
        "thank_you.html",
        user=user,
        election=election
    )


# ============================================================
# ALREADY VOTED
# ============================================================

@app.route("/already_voted/<int:election_id>")
def already_voted(election_id):
    if "user_id" not in session:
        return redirect(url_for("login"))

    election = get_election(election_id)
    if not election:
        flash("Election not found.", "danger")
        return redirect(url_for("dashboard"))

    conn = get_db()
    try:
        user = conn.execute(
            "SELECT * FROM users WHERE id = ?",
            (session["user_id"],)
        ).fetchone()
    finally:
        conn.close()

    if not user:
        session.clear()
        return redirect(url_for("login"))

    # Pass both variables explicitly; already_voted.html references user['name'].
    return render_template(
        "already_voted.html",
        user=user,
        election=election,
        election_id=election_id
    )

# ============================================================
# NOT ELIGIBLE
# ============================================================

@app.route(
    "/not_eligible"
)
def not_eligible():

    if "user_id" not in session:

        return redirect(
            url_for("login")
        )

    return render_template(
        "not_eligible.html"
    )


# ============================================================
# VOTING NOT STARTED
# ============================================================

@app.route(
    "/voting_not_started"
)
def voting_not_started():

    return render_template(
        "voting_not_started.html"
    )


# ============================================================
# VOTING ENDED
# ============================================================

@app.route(
    "/voting_ended"
)
def voting_ended():

    return render_template(
        "voting_ended.html"
    )


# ============================================================
# ELECTION STATUS API
# ============================================================

@app.route(
    "/election_status_api/<int:election_id>"
)
def election_status_api(
    election_id
):

    election = get_election(
        election_id
    )

    if not election:

        return jsonify({

            "status":
                "not_found",

            "remaining_seconds":
                0

        }), 404

    return jsonify({

        "status":
            election_status(
                election
            ),

        "remaining_seconds":
            election_remaining_seconds(
                election
            ),

        "election_id":
            election_id
    })


# ============================================================
# OLD STATUS API
# ============================================================

@app.route(
    "/voting_status_api"
)
def voting_status_api():

    status = voting_status()

    remaining = (
        voting_remaining_seconds()
    )

    return jsonify({

        "status":
            status,

        "remaining_seconds":
            remaining
    })


# ============================================================
# ELECTION RESULTS
# ============================================================

@app.route("/results/<int:election_id>")
def election_results(election_id):
    """Render accurate per-election totals directly from election_votes."""
    election = get_election(election_id)
    if not election:
        flash("Election not found.", "danger")
        return redirect(url_for("dashboard"))

    conn = get_db()
    try:
        # Count each candidate's votes only for this election. Keep candidates
        # with zero votes visible by using LEFT JOIN.
        candidates = conn.execute(
            """
            SELECT
                ec.id,
                ec.election_id,
                ec.name,
                ec.party,
                ec.party_symbol,
                ec.created_at,
                COALESCE(v.vote_count, 0) AS votes
            FROM election_candidates AS ec
            LEFT JOIN (
                SELECT candidate_id, election_id, COUNT(*) AS vote_count
                FROM election_votes
                WHERE election_id = ?
                GROUP BY candidate_id, election_id
            ) AS v
              ON v.candidate_id = ec.id
             AND v.election_id = ec.election_id
            WHERE ec.election_id = ?
            ORDER BY votes DESC, ec.id ASC
            """,
            (election_id, election_id)
        ).fetchall()

        total_row = conn.execute(
            """
            SELECT COUNT(*) AS total
            FROM election_votes
            WHERE election_id = ?
            """,
            (election_id,)
        ).fetchone()
        total_votes = int(total_row["total"] or 0)

        # Internal consistency check: candidate totals should add up to the
        # election's total. The total above remains the authoritative count.
        candidate_vote_sum = sum(int(c["votes"] or 0) for c in candidates)
        if candidate_vote_sum != total_votes:
            app.logger.warning(
                "Vote count mismatch for election %s: total=%s candidate_sum=%s",
                election_id, total_votes, candidate_vote_sum
            )
    finally:
        conn.close()

    status = election_status(election)
    winner = None
    is_tie = False
    if status == "ended" and total_votes > 0 and candidates:
        top_votes = int(candidates[0]["votes"] or 0)
        top_candidates = [c for c in candidates if int(c["votes"] or 0) == top_votes]
        is_tie = len(top_candidates) > 1
        if not is_tie:
            winner = top_candidates[0]

    return render_template(
        "results.html",
        election=election,
        candidates=candidates,
        total_votes=total_votes,
        winner=winner,
        is_tie=is_tie,
        voting_state=status
    )

# ============================================================
# LEGACY RESULTS ROUTE
# ============================================================

@app.route("/results")
def results():
    """Open the active election's results, or the latest election with votes."""
    conn = get_db()
    try:
        all_elections = conn.execute(
            """
            SELECT e.*,
                   (SELECT COUNT(*) FROM election_votes v
                    WHERE v.election_id = e.id) AS vote_count
            FROM elections e
            WHERE e.archived = 0
            ORDER BY e.id DESC
            """
        ).fetchall()
    finally:
        conn.close()

    if all_elections:
        # Prefer an election that is currently accepting votes.
        active = next((e for e in all_elections if election_status(e) == "active"), None)
        # Otherwise show the most recent election that actually has votes,
        # so /results does not silently open a newer empty election.
        with_votes = next((e for e in all_elections if int(e["vote_count"] or 0) > 0), None)
        election = active or with_votes or all_elections[0]
        return redirect(url_for("election_results", election_id=election["id"]))

    return render_template(
        "results.html",
        election=None,
        candidates=[],
        total_votes=0,
        winner=None,
        is_tie=False,
        voting_state="not_started"
    )


# ============================================================
# FORGOT PASSWORD
# ============================================================

@app.route(
    "/forgot_password",
    methods=[
        "GET",
        "POST"
    ]
)
def forgot_password():

    if request.method == "GET":

        return render_template(
            "forgot_password.html"
        )

    name = request.form.get(
        "name",
        ""
    ).strip()

    father_name = request.form.get(
        "father_name",
        ""
    ).strip()

    email = request.form.get(
        "email",
        ""
    ).strip().lower()

    mobile = re.sub(
        r"\D",
        "",
        request.form.get(
            "mobile",
            ""
        )
    )

    aadhaar = re.sub(
        r"\D",
        "",
        request.form.get(
            "aadhaar",
            ""
        )
    )

    if not all([
        name,
        father_name,
        email,
        mobile,
        aadhaar
    ]):

        flash(
            "Please fill all fields.",
            "danger"
        )

        return redirect(
            url_for(
                "forgot_password"
            )
        )

    conn = get_db()

    try:

        user = conn.execute(
            """
            SELECT *
            FROM users
            WHERE LOWER(email) = ?
            AND aadhaar = ?
            AND mobile = ?
            """,
            (
                email,
                aadhaar,
                mobile
            )
        ).fetchone()

        if not user:

            flash(
                "No matching voter account was found.",
                "danger"
            )

            return redirect(
                url_for(
                    "forgot_password"
                )
            )

        if (
            user["name"].strip().lower()
            !=
            name.lower()
            or
            (
                user["father_name"] or ""
            ).strip().lower()
            !=
            father_name.lower()
        ):

            flash(
                "Voter details do not match the registered account.",
                "danger"
            )

            return redirect(
                url_for(
                    "forgot_password"
                )
            )

        conn.execute(
            """
            INSERT INTO password_requests
            (
                name,
                father_name,
                email,
                mobile,
                aadhaar,
                status,
                request_date
            )
            VALUES (?, ?, ?, ?, ?, 'pending', ?)
            """,
            (
                name,
                father_name,
                email,
                mobile,
                aadhaar,
                datetime.now().isoformat()
            )
        )

        conn.commit()

        flash(
            "Password reset request sent to administrator for approval.",
            "success"
        )

        return redirect(
            url_for("login")
        )

    except sqlite3.Error as e:

        conn.rollback()

        print(
            "Forgot password database error:",
            e
        )

        flash(
            "Unable to submit password reset request.",
            "danger"
        )

        return redirect(
            url_for(
                "forgot_password"
            )
        )

    finally:

        conn.close()


# ============================================================
# ADMIN LOGIN
# ============================================================

@app.route(
    "/admin_login",
    methods=[
        "GET",
        "POST"
    ]
)
def admin_login():

    if request.method == "GET":

        return render_template(
            "admin_login.html"
        )

    username = request.form.get(
        "username",
        ""
    ).strip()

    password = request.form.get(
        "password",
        ""
    )

    conn = get_db()

    try:

        admin = conn.execute(
            """
            SELECT *
            FROM admin
            WHERE username = ?
            """,
            (
                username,
            )
        ).fetchone()

    finally:

        conn.close()

    if not admin:

        flash(
            "Invalid administrator credentials.",
            "danger"
        )

        return redirect(
            url_for("admin_login")
        )

    if not check_password_hash(
        admin["password"],
        password
    ):

        flash(
            "Invalid administrator credentials.",
            "danger"
        )

        return redirect(
            url_for("admin_login")
        )

    session.clear()

    session["admin_id"] = (
        admin["id"]
    )

    session["admin_username"] = (
        admin["username"]
    )

    return redirect(
        url_for("admin_dashboard")
    )


# ============================================================
# ADMIN DASHBOARD
# ============================================================

@app.route(
    "/admin_dashboard"
)
def admin_dashboard():

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    conn = get_db()

    try:

        total_registered = conn.execute(
            """
            SELECT COUNT(*) AS c
            FROM users
            """
        ).fetchone()["c"]

        total_eligible = conn.execute(
            """
            SELECT COUNT(*) AS c
            FROM users
            WHERE eligible = 1
            """
        ).fetchone()["c"]

        total_voted = conn.execute(
            """
            SELECT COUNT(DISTINCT user_id)
            FROM election_votes
            """
        ).fetchone()[0]

        total_not_voted = max(
            0,
            total_registered
            -
            total_voted
        )

        elections = conn.execute(
            """
            SELECT *
            FROM elections
            ORDER BY id DESC
            """
        ).fetchall()

        password_request_count = conn.execute(
            """
            SELECT COUNT(*) AS c
            FROM password_requests
            WHERE status = 'pending'
            """
        ).fetchone()["c"]

        candidates = conn.execute(
            """
            SELECT *
            FROM candidates
            ORDER BY id DESC
            """
        ).fetchall()

        voters = conn.execute(
            """
            SELECT *
            FROM users
            ORDER BY id DESC
            """
        ).fetchall()

        election_data = []

        for election in elections:

            voted_count = conn.execute(
                """
                SELECT COUNT(*)
                FROM election_votes
                WHERE election_id = ?
                """,
                (
                    election["id"],
                )
            ).fetchone()[0]

            candidate_count = conn.execute(
                """
                SELECT COUNT(*)
                FROM election_candidates
                WHERE election_id = ?
                """,
                (
                    election["id"],
                )
            ).fetchone()[0]

            # The dashboard template renders item.candidate_results.
            # Fetch candidates for THIS election and count votes for each one.
            candidate_results = conn.execute(
                """
                SELECT
                    ec.id,
                    ec.name,
                    ec.party,
                    ec.party_symbol,
                    COUNT(ev.id) AS votes
                FROM election_candidates AS ec
                LEFT JOIN election_votes AS ev
                    ON ev.candidate_id = ec.id
                    AND ev.election_id = ec.election_id
                WHERE ec.election_id = ?
                GROUP BY ec.id, ec.name, ec.party, ec.party_symbol
                ORDER BY ec.id
                """,
                (election["id"],)
            ).fetchall()

            election_data.append({

                "election":
                    election,

                "status":
                    election_status(
                        election
                    ),

                "voted_count":
                    voted_count,

                "candidate_count":
                    candidate_count,

                "candidate_results":
                    candidate_results
            })

    finally:

        conn.close()

    return render_template(
        "admin_dashboard.html",

        total_registered=
            total_registered,

        total_voted=
            total_voted,

        total_not_voted=
            total_not_voted,

        total_eligible=
            total_eligible,

        elections=
            election_data,

        candidates=
            candidates,

        voters=
            voters,

        password_request_count=
            password_request_count,

        voting_state=
            voting_status(),

        remaining_seconds=
            voting_remaining_seconds()
    )


# ============================================================
# ADMIN CREATE ELECTION
# ============================================================

@app.route(
    "/admin_create_election",
    methods=["POST"]
)
def admin_create_election():

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    name = request.form.get(
        "election_name",
        ""
    ).strip()

    description = request.form.get(
        "description",
        ""
    ).strip()

    election_type = request.form.get(
        "election_type",
        "general"
    ).strip()

    scope = request.form.get(
        "scope",
        "all_india"
    ).strip().lower()

    state = request.form.get(
        "state",
        ""
    ).strip()

    district = request.form.get(
        "district",
        ""
    ).strip()

    start_date = request.form.get(
        "start_date",
        ""
    ).strip()

    start_time = request.form.get(
        "start_time",
        ""
    ).strip()

    duration_hours = request.form.get(
        "duration_hours",
        "0"
    ).strip()

    duration_minutes = request.form.get(
        "duration_minutes",
        "0"
    ).strip()

    if not name:

        flash(
            "Election name is required.",
            "danger"
        )

        return redirect(
            url_for("admin_dashboard")
        )

    if scope not in [
        "all_india",
        "state",
        "district"
    ]:

        flash(
            "Invalid election scope.",
            "danger"
        )

        return redirect(
            url_for("admin_dashboard")
        )

    if scope == "all_india":

        state = None
        district = None

    elif scope == "state":

        if state not in INDIAN_STATES:

            flash(
                "Please select a valid state/UT.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        district = "All Districts"

    elif scope == "district":

        if state not in INDIAN_STATES:

            flash(
                "Please select a valid state/UT.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        valid_districts = (
            INDIA_DISTRICTS.get(
                state,
                []
            )
        )

        if district in [
            "",
            "All Districts"
        ]:

            district = "All Districts"

        elif (
            valid_districts
            and
            district not in valid_districts
        ):

            flash(
                "Invalid district for selected state.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

    start_datetime = None

    if start_date or start_time:

        if not (
            start_date
            and
            start_time
        ):

            flash(
                "Both start date and start time are required.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        try:

            start_dt = datetime.strptime(
                f"{start_date} {start_time}",
                "%Y-%m-%d %H:%M"
            )

            if start_dt < datetime.now():

                flash(
                    "Election start date/time cannot be in the past.",
                    "danger"
                )

                return redirect(
                    url_for("admin_dashboard")
                )

            start_datetime = (
                start_dt.isoformat()
            )

        except ValueError:

            flash(
                "Invalid election date/time.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

    try:

        hours = int(
            duration_hours or 0
        )

        minutes = int(
            duration_minutes or 0
        )

    except (
        ValueError,
        TypeError
    ):

        flash(
            "Invalid election duration.",
            "danger"
        )

        return redirect(
            url_for("admin_dashboard")
        )

    if (
        hours < 0
        or
        minutes < 0
    ):

        flash(
            "Election duration cannot be negative.",
            "danger"
        )

        return redirect(
            url_for("admin_dashboard")
        )

    total_minutes = (
        hours * 60
        +
        minutes
    )

    duration_seconds = (
        total_minutes * 60
    )

    if (
        start_datetime
        and
        duration_seconds > 0
    ):

        status = "scheduled"

    else:

        status = "draft"

    conn = get_db()

    try:

        cursor = conn.execute(
            """
            INSERT INTO elections
            (
                name,
                description,
                election_type,
                scope,
                state,
                district,
                start_datetime,
                duration_seconds,
                status,
                archived,
                created_at,
                updated_at
            )
            VALUES
            (
                ?, ?, ?, ?, ?, ?,
                ?, ?, ?, 0, ?, ?
            )
            """,
            (
                name,
                description,
                election_type,
                scope,
                state,
                district,
                start_datetime,
                duration_seconds,
                status,
                datetime.now().isoformat(),
                datetime.now().isoformat()
            )
        )

        election_id = (
            cursor.lastrowid
        )

        conn.commit()

        flash(
            f"Election '{name}' created successfully.",
            "success"
        )

        return redirect(
            url_for(
                "admin_manage_election",
                election_id=election_id
            )
        )

    except sqlite3.Error as e:

        conn.rollback()

        print(
            "Election creation error:",
            e
        )

        flash(
            "Unable to create election.",
            "danger"
        )

        return redirect(
            url_for("admin_dashboard")
        )

    finally:

        conn.close()


# ============================================================
# ADMIN ELECTION DETAILS (READ-ONLY HISTORY AND RESULTS)
# ============================================================

@app.route("/admin/election/<int:election_id>/details")
def admin_election_details(election_id):
    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    election = get_election(election_id)
    if not election:
        flash("Election not found.", "danger")
        return redirect(url_for("admin_dashboard"))

    conn = get_db()
    try:
        candidates = conn.execute(
            """SELECT ec.*, COUNT(ev.id) AS votes
               FROM election_candidates ec
               LEFT JOIN election_votes ev
                 ON ev.candidate_id = ec.id AND ev.election_id = ec.election_id
               WHERE ec.election_id = ?
               GROUP BY ec.id
               ORDER BY votes DESC, ec.id ASC""",
            (election_id,)
        ).fetchall()
        total_votes = conn.execute(
            "SELECT COUNT(*) FROM election_votes WHERE election_id = ?",
            (election_id,)
        ).fetchone()[0]
    finally:
        conn.close()

    status = election_status(election)
    winner = candidates[0] if status in ("ended", "archived") and candidates and total_votes > 0 else None
    start_display = "Not scheduled"
    end_display = "Not scheduled"
    duration_seconds = int(election["duration_seconds"] or 0)
    duration_display = "Not set"
    start_dt = None
    if election["start_datetime"]:
        try:
            start_dt = datetime.fromisoformat(election["start_datetime"])
            start_display = start_dt.strftime("%d %b %Y, %I:%M %p")
            end_dt = start_dt + timedelta(seconds=duration_seconds)
            end_display = end_dt.strftime("%d %b %Y, %I:%M %p")
        except (ValueError, TypeError):
            pass
    if duration_seconds > 0:
        hours, remainder = divmod(duration_seconds, 3600)
        minutes = remainder // 60
        duration_display = f"{hours} hour(s), {minutes} minute(s)"

    return render_template(
        "admin_election_details.html",
        election=election,
        candidates=candidates,
        total_votes=total_votes,
        status=status,
        winner=winner,
        start_display=start_display,
        end_display=end_display,
        duration_display=duration_display,
    )


# ============================================================
# ADMIN MANAGE ELECTION
# ============================================================

@app.route(
    "/admin_manage_election/<int:election_id>"
)
def admin_manage_election(
    election_id
):

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    election = get_election(
        election_id
    )

    if not election:

        flash(
            "Election not found.",
            "danger"
        )

        return redirect(
            url_for("admin_dashboard")
        )

    conn = get_db()

    try:

        candidates = conn.execute(
            """
            SELECT
                ec.*,
                COUNT(ev.id) AS votes
            FROM election_candidates ec
            LEFT JOIN election_votes ev
                ON ev.candidate_id = ec.id
            WHERE ec.election_id = ?
            GROUP BY ec.id
            ORDER BY ec.id
            """,
            (
                election_id,
            )
        ).fetchall()

        voters_count = conn.execute(
            """
            SELECT COUNT(*)
            FROM election_votes
            WHERE election_id = ?
            """,
            (
                election_id,
            )
        ).fetchone()[0]

        eligible_count = conn.execute(
            """
            SELECT COUNT(*)
            FROM users
            WHERE eligible = 1
            """
        ).fetchone()[0]

    finally:

        conn.close()

    return render_template(
        "admin_manage_election.html",
        election=election,
        candidates=candidates,
        voted_count=voters_count,
        eligible_count=eligible_count,
        election_status=election_status(
            election
        )
    )


# ============================================================
# ADMIN START ELECTION
# ============================================================

@app.route(
    "/admin_start_election/<int:election_id>",
    methods=["POST"]
)
def admin_start_election(election_id):
    """Start an existing election immediately without replacing the database."""

    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    conn = get_db()
    try:
        conn.execute("BEGIN IMMEDIATE")

        election = conn.execute(
            "SELECT * FROM elections WHERE id = ?",
            (election_id,)
        ).fetchone()

        if election is None:
            conn.rollback()
            flash("Election not found.", "danger")
            return redirect(url_for("admin_dashboard"))

        if int(election["archived"] or 0) == 1:
            conn.rollback()
            flash("An archived election cannot be started.", "danger")
            return redirect(url_for("admin_manage_election", election_id=election_id))

        status_now = election_status(election)
        if status_now == "active":
            conn.rollback()
            flash("This election is already active.", "warning")
            return redirect(url_for("admin_manage_election", election_id=election_id))

        if status_now == "ended":
            conn.rollback()
            flash("This election has already ended and cannot be restarted.", "danger")
            return redirect(url_for("admin_manage_election", election_id=election_id))

        candidate_count = conn.execute(
            "SELECT COUNT(*) FROM election_candidates WHERE election_id = ?",
            (election_id,)
        ).fetchone()[0]

        if candidate_count < 2:
            conn.rollback()
            flash("Add at least two candidates before starting the election.", "danger")
            return redirect(url_for("admin_manage_election", election_id=election_id))

        duration_seconds = int(election["duration_seconds"] or 0)
        if duration_seconds <= 0:
            conn.rollback()
            flash("Set a valid election duration before starting.", "danger")
            return redirect(url_for("admin_manage_election", election_id=election_id))

        # The admin's Start button starts voting now. Reset the scheduled start
        # time so election_status() and the remaining-time timer agree.
        now = datetime.now()
        conn.execute(
            """UPDATE elections
               SET start_datetime = ?, status = 'active', updated_at = ?
               WHERE id = ?""",
            (now.isoformat(), now.isoformat(), election_id)
        )
        conn.commit()
        flash("Election started successfully.", "success")

    except (sqlite3.Error, ValueError, TypeError):
        conn.rollback()
        app.logger.exception("Failed to start election %s", election_id)
        flash("Could not start the election. Check the schedule and application log.", "danger")

    finally:
        conn.close()

    return redirect(url_for("admin_manage_election", election_id=election_id))


# ============================================================
# ADMIN ADD ELECTION CANDIDATE
# ============================================================

@app.route(
    "/admin_add_election_candidate/<int:election_id>",
    methods=["POST"]
)
@app.route(
    "/admin/election/<int:election_id>/candidate/add",
    methods=["POST"]
)
def admin_add_election_candidate(election_id):

    # --------------------------------------------------------
    # ADMIN LOGIN CHECK
    # --------------------------------------------------------

    if "admin_id" not in session:
        return redirect(
            url_for("admin_login")
        )

    locked_election = get_election(election_id)
    if not locked_election:
        flash("Election not found.", "danger")
        return redirect(url_for("admin_dashboard"))
    if election_status(locked_election) in ("active", "ended", "archived"):
        flash("This election is locked. Candidates cannot be changed after voting starts or ends.", "danger")
        return redirect(url_for("admin_election_details", election_id=election_id))

    # --------------------------------------------------------
    # GET FORM DATA
    # --------------------------------------------------------
    # Supports both old and new form field names.
    # Old:
    # candidate_name
    # party_name
    #
    # New:
    # name
    # party
    # --------------------------------------------------------

    candidate_name = request.form.get(
        "candidate_name"
    )

    if not candidate_name:
        candidate_name = request.form.get(
            "name",
            ""
        )

    candidate_name = candidate_name.strip()

    party = request.form.get(
        "party_name"
    )

    if not party:
        party = request.form.get(
            "party",
            ""
        )

    party = party.strip()

    party_symbol = request.form.get(
        "party_symbol",
        ""
    ).strip()

    # --------------------------------------------------------
    # CHECK ELECTION
    # --------------------------------------------------------

    election = get_election(
        election_id
    )

    if not election:

        flash(
            "Election not found.",
            "danger"
        )

        return redirect(
            url_for("admin_dashboard")
        )

    # --------------------------------------------------------
    # CHECK ARCHIVED ELECTION
    # --------------------------------------------------------

    try:

        if int(
            election["archived"] or 0
        ) == 1:

            flash(
                "Candidate cannot be added to an archived election.",
                "danger"
            )

            return redirect(
                url_for(
                    "admin_manage_election",
                    election_id=election_id
                )
            )

    except (KeyError, TypeError, ValueError):

        pass

    # --------------------------------------------------------
    # CHECK ELECTION STATUS
    # --------------------------------------------------------

    try:

        current_status = election_status(
            election
        )

        if current_status == "active":

            flash(
                "Candidate cannot be added while the election is active.",
                "danger"
            )

            return redirect(
                url_for(
                    "admin_manage_election",
                    election_id=election_id
                )
            )

    except Exception as e:

        print(
            "Election status check error:",
            e
        )

    # --------------------------------------------------------
    # VALIDATE CANDIDATE NAME
    # --------------------------------------------------------

    if not candidate_name:

        flash(
            "Candidate name is required.",
            "danger"
        )

        return redirect(
            url_for(
                "admin_manage_election",
                election_id=election_id
            )
        )

    # --------------------------------------------------------
    # VALIDATE PARTY
    # --------------------------------------------------------

    if not party:

        flash(
            "Party name is required.",
            "danger"
        )

        return redirect(
            url_for(
                "admin_manage_election",
                election_id=election_id
            )
        )

    # --------------------------------------------------------
    # VALIDATE PARTY SYMBOL
    # --------------------------------------------------------

    if not party_symbol:

        flash(
            "Party symbol is required.",
            "danger"
        )

        return redirect(
            url_for(
                "admin_manage_election",
                election_id=election_id
            )
        )

    # --------------------------------------------------------
    # DATABASE CONNECTION
    # --------------------------------------------------------

    conn = get_db()

    try:

        # ----------------------------------------------------
        # CHECK DUPLICATE CANDIDATE
        # ----------------------------------------------------

        existing_candidate = conn.execute(
            """
            SELECT id
            FROM election_candidates
            WHERE election_id = ?
              AND LOWER(TRIM(name))
                  = LOWER(TRIM(?))
            LIMIT 1
            """,
            (
                election_id,
                candidate_name
            )
        ).fetchone()

        if existing_candidate:

            flash(
                "A candidate with this name already exists in this election.",
                "warning"
            )

            return redirect(
                url_for(
                    "admin_manage_election",
                    election_id=election_id
                )
            )

        # ----------------------------------------------------
        # ADD CANDIDATE
        # ----------------------------------------------------

        now = datetime.now().strftime(
            "%Y-%m-%d %H:%M:%S"
        )

        conn.execute(
            """
            INSERT INTO election_candidates
            (
                election_id,
                name,
                party,
                party_symbol,
                created_at
            )
            VALUES
            (
                ?,
                ?,
                ?,
                ?,
                ?
            )
            """,
            (
                election_id,
                candidate_name,
                party,
                party_symbol,
                now
            )
        )

        # ----------------------------------------------------
        # SAVE CHANGES
        # ----------------------------------------------------

        conn.commit()

        flash(
            f"Candidate '{candidate_name}' added successfully.",
            "success"
        )

    # --------------------------------------------------------
    # SQLITE INTEGRITY ERROR
    # --------------------------------------------------------

    except sqlite3.IntegrityError as e:

        conn.rollback()

        print(
            "Add election candidate integrity error:",
            e
        )

        flash(
            "Candidate could not be added because of existing linked data.",
            "danger"
        )

    # --------------------------------------------------------
    # SQLITE DATABASE ERROR
    # --------------------------------------------------------

    except sqlite3.Error as e:

        conn.rollback()

        print(
            "Add election candidate database error:",
            e
        )

        flash(
            "Database error while adding candidate.",
            "danger"
        )

    # --------------------------------------------------------
    # GENERAL ERROR
    # --------------------------------------------------------

    except Exception as e:

        conn.rollback()

        print(
            "Add election candidate error:",
            e
        )

        flash(
            "Unable to add candidate.",
            "danger"
        )

    # --------------------------------------------------------
    # CLOSE DATABASE
    # --------------------------------------------------------

    finally:

        conn.close()

    # --------------------------------------------------------
    # RETURN TO ADMIN MANAGE ELECTION
    # --------------------------------------------------------

    return redirect(
        url_for(
            "admin_manage_election",
            election_id=election_id
        )
    )
 



# ============================================================
# LEGACY ADMIN DELETE CANDIDATE
# ============================================================

@app.route(
    "/admin/delete-candidate/<int:candidate_id>",
    methods=["POST"]
)
def admin_delete_candidate(candidate_id):

    if "admin_id" not in session:
        return redirect(
            url_for("admin_login")
        )

    conn = get_db()

    try:

        candidate = conn.execute(
            """
            SELECT *
            FROM candidates
            WHERE id = ?
            """,
            (
                candidate_id,
            )
        ).fetchone()

        if not candidate:

            flash(
                "Candidate not found.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        # Check whether this candidate already has votes
        voted = conn.execute(
            """
            SELECT COUNT(*)
            FROM users
            WHERE voted_candidate_id = ?
            """,
            (
                candidate_id,
            )
        ).fetchone()[0]

        if voted > 0:

            flash(
                "Candidate cannot be deleted because votes have already been recorded.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        # Delete legacy candidate
        conn.execute(
            """
            DELETE FROM candidates
            WHERE id = ?
            """,
            (
                candidate_id,
            )
        )

        conn.commit()

        flash(
            "Candidate deleted successfully.",
            "success"
        )

    except sqlite3.IntegrityError as e:

        conn.rollback()

        print(
            "Legacy candidate deletion integrity error:",
            e
        )

        flash(
            "Candidate cannot be deleted because it is linked with existing data.",
            "danger"
        )

    except sqlite3.Error as e:

        conn.rollback()

        print(
            "Legacy candidate deletion error:",
            e
        )

        flash(
            "Unable to delete candidate.",
            "danger"
        )

    finally:

        conn.close()

    return redirect(
        url_for("admin_dashboard")
    )
@app.route(
    "/admin_update_election_schedule/<int:election_id>",
    methods=["POST"]
)
def admin_update_election_schedule(
    election_id
):

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    locked_election = get_election(election_id)
    if not locked_election:
        flash("Election not found.", "danger")
        return redirect(url_for("admin_dashboard"))
    if election_status(locked_election) in ("active", "ended", "archived"):
        flash("This election is locked. Its schedule cannot be changed after voting starts or ends.", "danger")
        return redirect(url_for("admin_election_details", election_id=election_id))

    start_date = request.form.get(
        "start_date",
        ""
    ).strip()

    start_time = request.form.get(
        "start_time",
        ""
    ).strip()

    try:

        hours = int(
            request.form.get(
                "duration_hours",
                "0"
            )
            or
            0
        )

        minutes = int(
            request.form.get(
                "duration_minutes",
                "0"
            )
            or
            0
        )

    except (
        ValueError,
        TypeError
    ):

        flash(
            "Invalid duration.",
            "danger"
        )

        return redirect(
            url_for(
                "admin_manage_election",
                election_id=election_id
            )
        )

    if (
        hours < 0
        or
        minutes < 0
    ):

        flash(
            "Duration cannot be negative.",
            "danger"
        )

        return redirect(
            url_for(
                "admin_manage_election",
                election_id=election_id
            )
        )

    total_minutes = (
        hours * 60
        +
        minutes
    )

    if total_minutes <= 0:

        flash(
            "Duration must be greater than 0 minutes.",
            "danger"
        )

        return redirect(
            url_for(
                "admin_manage_election",
                election_id=election_id
            )
        )

    if not start_date or not start_time:

        flash(
            "Start date and time are required.",
            "danger"
        )

        return redirect(
            url_for(
                "admin_manage_election",
                election_id=election_id
            )
        )

    try:

        start_dt = datetime.strptime(
            f"{start_date} {start_time}",
            "%Y-%m-%d %H:%M"
        )

    except ValueError:

        flash(
            "Invalid date/time.",
            "danger"
        )

        return redirect(
            url_for(
                "admin_manage_election",
                election_id=election_id
            )
        )

    if start_dt < datetime.now():

        flash(
            "Election start time cannot be in the past.",
            "danger"
        )

        return redirect(
            url_for(
                "admin_manage_election",
                election_id=election_id
            )
        )

    duration_seconds = (
        total_minutes * 60
    )

    conn = get_db()

    try:

        result = conn.execute(
            """
            UPDATE elections
            SET
                start_datetime = ?,
                duration_seconds = ?,
                status = 'scheduled',
                updated_at = ?
            WHERE id = ?
            """,
            (
                start_dt.isoformat(),
                duration_seconds,
                datetime.now().isoformat(),
                election_id
            )
        )

        if result.rowcount != 1:

            conn.rollback()

            flash(
                "Election not found.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        conn.commit()

        flash(
            "Election schedule updated successfully.",
            "success"
        )

    except sqlite3.Error as e:

        conn.rollback()

        print(
            "Election schedule error:",
            e
        )

        flash(
            "Unable to update election schedule.",
            "danger"
        )

    finally:

        conn.close()

    return redirect(
        url_for(
            "admin_manage_election",
            election_id=election_id
        )
    )

# ============================================================
# CREATE A NEW ELECTION AND ADD ITS FIRST CANDIDATE
# ============================================================

@app.route(
    "/admin/create-election-and-add-candidate",
    methods=["POST"]
)
def admin_create_election_and_add_candidate():
    """Create a scheduled election and save each candidate's symbol image."""
    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    election_name = request.form.get("election_name", "").strip()
    election_type = request.form.get("election_type", "").strip()
    start_date = request.form.get("start_date", "").strip()
    start_time = request.form.get("start_time", "").strip()
    scope = request.form.get("scope", "all_india").strip().lower()
    state = request.form.get("state", "").strip()
    district = request.form.get("district", "").strip()

    try:
        hours = int(request.form.get("duration_hours", "0") or 0)
        minutes = int(request.form.get("duration_minutes", "0") or 0)
    except (TypeError, ValueError):
        flash("Please enter a valid election duration.", "danger")
        return redirect(url_for("admin_dashboard"))

    if not election_name or not election_type:
        flash("Election name and type are required.", "danger")
        return redirect(url_for("admin_dashboard"))
    if not start_date or not start_time:
        flash("Voting date and start time are required.", "danger")
        return redirect(url_for("admin_dashboard"))
    if hours < 0 or minutes < 0 or minutes > 59 or (hours * 60 + minutes) <= 0:
        flash("Election duration must be greater than zero.", "danger")
        return redirect(url_for("admin_dashboard"))

    if scope not in ("all_india", "state", "district"):
        flash("Please select a valid voting eligibility area.", "danger")
        return redirect(url_for("admin_dashboard"))
    if scope in ("state", "district") and not state:
        flash("Please select a state for this election.", "danger")
        return redirect(url_for("admin_dashboard"))
    if scope == "district" and not district:
        flash("Please select a district for this election.", "danger")
        return redirect(url_for("admin_dashboard"))

    try:
        start_dt = datetime.strptime(f"{start_date} {start_time}", "%Y-%m-%d %H:%M")
    except ValueError:
        flash("Please enter a valid voting date and time.", "danger")
        return redirect(url_for("admin_dashboard"))
    if start_dt <= datetime.now():
        flash("Voting date and time must be in the future.", "danger")
        return redirect(url_for("admin_dashboard"))

    names = request.form.getlist("name")
    parties = request.form.getlist("party")
    symbol_files = request.files.getlist("party_symbol_file")
    candidate_rows = []
    row_count = max(len(names), len(parties), len(symbol_files))

    for i in range(row_count):
        name = names[i].strip() if i < len(names) else ""
        party = parties[i].strip() if i < len(parties) else ""
        symbol_file = symbol_files[i] if i < len(symbol_files) else None
        has_file = bool(symbol_file and symbol_file.filename and symbol_file.filename.strip())
        # Ignore a truly empty extra row, but reject any partially completed row.
        if not name and not party and not has_file:
            continue
        if not name or not party or not has_file:
            flash("Fill in the name, party and upload a symbol image for every candidate row.", "danger")
            return redirect(url_for("admin_dashboard"))
        original_name = secure_filename(symbol_file.filename)
        extension = original_name.rsplit(".", 1)[-1].lower() if "." in original_name else ""
        if extension not in {"jpg", "jpeg", "png", "webp"}:
            flash(f"Symbol image for {name} must be JPG, JPEG, PNG or WEBP.", "danger")
            return redirect(url_for("admin_dashboard"))
        image_bytes = symbol_file.read()
        if not image_bytes:
            flash(f"Please choose a valid symbol image for {name}.", "danger")
            return redirect(url_for("admin_dashboard"))
        if len(image_bytes) > 5 * 1024 * 1024:
            flash(f"Symbol image for {name} must be 5 MB or smaller.", "danger")
            return redirect(url_for("admin_dashboard"))
        # Keep the bytes in memory until the database transaction succeeds.
        candidate_rows.append({
            "name": name,
            "party": party,
            "extension": extension,
            "image_bytes": image_bytes,
        })

    if not candidate_rows:
        flash("Add at least one candidate with name, party and symbol image before creating the election.", "danger")
        return redirect(url_for("admin_dashboard"))

    conn = get_db()
    saved_paths = []
    try:
        conn.execute("BEGIN IMMEDIATE")
        existing = conn.execute(
            "SELECT id FROM elections WHERE LOWER(TRIM(name)) = LOWER(TRIM(?)) AND LOWER(TRIM(election_type)) = LOWER(TRIM(?)) AND COALESCE(archived, 0) = 0 ORDER BY id DESC LIMIT 1",
            (election_name, election_type)
        ).fetchone()
        if existing:
            conn.rollback()
            flash("An election with this name and type already exists. Open its details instead.", "warning")
            return redirect(url_for("admin_election_details", election_id=existing["id"]))

        now = datetime.now().isoformat(timespec="seconds")
        duration_seconds = (hours * 60 + minutes) * 60
        cursor = conn.execute(
            """INSERT INTO elections (
                name, description, election_type, scope, state, district,
                start_datetime, duration_seconds, status, archived, created_at, updated_at
            ) VALUES (?, '', ?, ?, ?, ?, ?, ?, 'scheduled', 0, ?, ?)""",
            (election_name, election_type, scope, state or None,
             district or None, start_dt.isoformat(timespec="seconds"),
             duration_seconds, now, now)
        )
        election_id = cursor.lastrowid

        for row in candidate_rows:
            filename = f"election_{election_id}_{secrets.token_hex(12)}.{row['extension']}"
            absolute_path = os.path.join(SYMBOL_UPLOAD_FOLDER, filename)
            with open(absolute_path, "wb") as image_out:
                image_out.write(row["image_bytes"])
            saved_paths.append(absolute_path)
            # Store a URL-friendly relative path in party_symbol.
            symbol_path = f"uploads/symbols/{filename}"
            conn.execute(
                "INSERT INTO election_candidates (election_id, name, party, party_symbol, created_at) VALUES (?, ?, ?, ?, ?)",
                (election_id, row["name"], row["party"], symbol_path, now)
            )

        conn.commit()
        flash(f"Election '{election_name}' created with {len(candidate_rows)} candidate(s). It is now listed under Upcoming Elections.", "success")
        return redirect(url_for("admin_dashboard"))
    except (sqlite3.Error, OSError) as e:
        conn.rollback()
        for saved_path in saved_paths:
            try:
                os.remove(saved_path)
            except OSError:
                pass
        app.logger.exception("Create election failed")
        flash("Unable to create the election or save a symbol image. Check the Flask terminal.", "danger")
    finally:
        conn.close()
    return redirect(url_for("admin_dashboard"))


# ============================================================
# DELETE ELECTION CANDIDATE
# ============================================================

@app.route(
    "/admin/election/<int:election_id>/candidate/delete/<int:candidate_id>",
    methods=["POST"]
)
def admin_delete_election_candidate(
    election_id,
    candidate_id
):

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    locked_election = get_election(election_id)
    if not locked_election:
        flash("Election not found.", "danger")
        return redirect(url_for("admin_dashboard"))
    if election_status(locked_election) in ("active", "ended", "archived"):
        flash("This election is locked. Candidates cannot be deleted after voting starts or ends.", "danger")
        return redirect(url_for("admin_election_details", election_id=election_id))

    conn = get_db()

    try:

        election = conn.execute(
            """
            SELECT *
            FROM elections
            WHERE id = ?
            """,
            (election_id,)
        ).fetchone()

        if not election:

            flash(
                "Election not found.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        current_status = election_status(election)

        if current_status == "active":

            flash(
                "Candidates cannot be deleted while the election is active.",
                "danger"
            )

            return redirect(
                url_for(
                    "admin_manage_election",
                    election_id=election_id
                )
            )

        candidate = conn.execute(
            """
            SELECT *
            FROM election_candidates
            WHERE id = ?
            AND election_id = ?
            """,
            (
                candidate_id,
                election_id
            )
        ).fetchone()

        if not candidate:

            flash(
                "Candidate not found.",
                "danger"
            )

            return redirect(
                url_for(
                    "admin_manage_election",
                    election_id=election_id
                )
            )

        vote_count = conn.execute(
            """
            SELECT COUNT(*)
            FROM election_votes
            WHERE election_id = ?
            AND candidate_id = ?
            """,
            (
                election_id,
                candidate_id
            )
        ).fetchone()[0]

        if vote_count > 0:

            flash(
                "Candidate cannot be deleted because votes have already been recorded.",
                "danger"
            )

            return redirect(
                url_for(
                    "admin_manage_election",
                    election_id=election_id
                )
            )

        conn.execute(
            """
            DELETE FROM election_candidates
            WHERE id = ?
            AND election_id = ?
            """,
            (
                candidate_id,
                election_id
            )
        )

        conn.commit()

        flash(
            "Candidate deleted successfully.",
            "success"
        )

    except sqlite3.IntegrityError as e:

        conn.rollback()

        print(
            "Election candidate deletion integrity error:",
            e
        )

        flash(
            "Candidate cannot be deleted because it is linked with existing data.",
            "danger"
        )

    except sqlite3.Error as e:

        conn.rollback()

        print(
            "Election candidate deletion database error:",
            e
        )

        flash(
            "Unable to delete candidate.",
            "danger"
        )

    finally:

        conn.close()

    return redirect(
        url_for(
            "admin_manage_election",
            election_id=election_id
        )
    )

# ============================================================
# ADMIN ARCHIVE ELECTION
# ============================================================

@app.route(
    "/admin_archive_election/<int:election_id>",
    methods=["POST"]
)
def admin_archive_election(
    election_id
):

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    conn = get_db()

    try:

        election = conn.execute(
            """
            SELECT *
            FROM elections
            WHERE id = ?
            """,
            (
                election_id,
            )
        ).fetchone()

        if not election:

            flash(
                "Election not found.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        if election_status(election) == "active":

            flash(
                "Active election cannot be archived.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        result = conn.execute(
            """
            UPDATE elections
            SET
                archived = 1,
                status = 'archived',
                updated_at = ?
            WHERE id = ?
            """,
            (
                datetime.now().isoformat(),
                election_id
            )
        )

        if result.rowcount != 1:

            conn.rollback()

            flash(
                "Election not found.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        conn.commit()

        flash(
            "Election archived successfully. Its data has been preserved.",
            "success"
        )

    except sqlite3.Error as e:

        conn.rollback()

        print(
            "Election archive error:",
            e
        )

        flash(
            "Unable to archive election.",
            "danger"
        )

    finally:

        conn.close()

    return redirect(
        url_for("admin_dashboard")
    )


# ============================================================
# ADMIN DELETE ELECTION
# ============================================================

@app.route(
    "/admin_delete_election/<int:election_id>",
    methods=["POST"]
)
def admin_delete_election(election_id):
    """Permanently delete an election and all election-specific data.

    Voter accounts are deliberately preserved. Deletion is irreversible.
    """
    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    conn = get_db()
    try:
        conn.execute("BEGIN IMMEDIATE")
        election = conn.execute(
            "SELECT id, name FROM elections WHERE id = ?",
            (election_id,)
        ).fetchone()

        if election is None:
            conn.rollback()
            flash("Election not found. It may already have been deleted.", "warning")
            return redirect(url_for("admin_dashboard"))

        election_row = conn.execute(
            "SELECT * FROM elections WHERE id = ?", (election_id,)
        ).fetchone()
        # Protect only elections that are actively accepting votes.
        # Upcoming/not-started elections may be permanently deleted by admin.
        # Ended and archived elections may also be deleted from Previous Elections.
        current_status = election_status(election_row)
        if current_status == "active":
            conn.rollback()
            flash(
                "A live election cannot be permanently deleted. End the election first, then delete it from Previous Elections.",
                "danger"
            )
            return redirect(url_for("admin_dashboard"))

        # Remove rows from any additional election-specific table first.
        # These may reference votes/candidates and otherwise block their deletion.
        known_children = (
            "election_blockchain",
            "election_votes",
            "election_candidates",
        )
        protected = {"users", "elections", *known_children}
        table_rows = conn.execute(
            "SELECT name FROM sqlite_master WHERE type = 'table' AND name NOT LIKE 'sqlite_%'"
        ).fetchall()
        for table_row in table_rows:
            table_name = table_row["name"]
            if table_name in protected or not column_exists(conn, table_name, "election_id"):
                continue
            # Quote table names safely; they originate from sqlite_master.
            quoted_name = '"' + table_name.replace('"', '""') + '"'
            conn.execute(
                f"DELETE FROM {quoted_name} WHERE election_id = ?",
                (election_id,)
            )

        # Explicit order for the core election tables (dependent rows first).
        for table_name in known_children:
            if table_exists(conn, table_name) and column_exists(conn, table_name, "election_id"):
                conn.execute(
                    f'DELETE FROM "{table_name}" WHERE election_id = ?',
                    (election_id,)
                )

        cursor = conn.execute(
            "DELETE FROM elections WHERE id = ?",
            (election_id,)
        )
        if cursor.rowcount != 1:
            raise sqlite3.IntegrityError("Election row was not deleted")

        conn.commit()
        print(f"[ADMIN] Permanently deleted election id={election_id}, name={election['name']!r}")
        flash(
            f'Election "{election["name"]}" and its election-specific data were permanently deleted. Voter accounts were preserved.',
            "success"
        )

    except sqlite3.Error as e:
        conn.rollback()
        print("Election deletion error:", repr(e))
        flash(
            f"Election could not be deleted: {e}. No partial changes were saved; check the Flask terminal for details.",
            "danger"
        )
    finally:
        conn.close()

    return redirect(url_for("admin_dashboard"))


# ============================================================
# ADMIN ELECTION RESULTS
# ============================================================

@app.route(
    "/admin_election_results/<int:election_id>"
)
def admin_election_results(
    election_id
):

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    return redirect(
        url_for(
            "election_results",
            election_id=election_id
        )
    )


# ============================================================
# ADMIN ELECTION BLOCKCHAIN
# ============================================================

@app.route(
    "/admin_election_blockchain/<int:election_id>"
)
def admin_election_blockchain(election_id):
    """Display a selected election's blockchain and provide an election selector."""
    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    conn = get_db()
    try:
        # Include every retained election, including archived/previous elections.
        elections = conn.execute(
            "SELECT id, name, status, archived FROM elections ORDER BY id DESC"
        ).fetchall()

        election = conn.execute(
            "SELECT * FROM elections WHERE id = ?",
            (election_id,)
        ).fetchone()

        if election is None:
            flash("Election not found.", "danger")
            return redirect(url_for("blockchain"))

        blocks = conn.execute(
            """
            SELECT *
            FROM election_blockchain
            WHERE election_id = ?
            ORDER BY id DESC
            """,
            (election_id,)
        ).fetchall()
    finally:
        conn.close()

    blockchain_valid, blockchain_message = verify_election_blockchain(election_id)
    if not blocks and blockchain_valid:
        blockchain_message = "No blockchain blocks are stored for this election yet."

    return render_template(
        "blockchain.html",
        election=election,
        elections=elections,
        selected_election_id=election_id,
        blocks=blocks,
        blockchain_valid=blockchain_valid,
        blockchain_message=blockchain_message
    )

# ============================================================
# ADMIN VOTERS
# ============================================================

@app.route(
    "/admin_voters"
)
def admin_voters():

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    conn = get_db()

    try:

        voters = conn.execute(
            """
            SELECT *
            FROM users
            ORDER BY id DESC
            """
        ).fetchall()

    finally:

        conn.close()

    return render_template(
        "admin_voters.html",
        voters=voters
    )


# ============================================================
# ADMIN VOTER DETAILS
# ============================================================

@app.route(
    "/admin_voter_details/<int:user_id>"
)
def admin_voter_details(user_id):
    """Show voter profile and participation status without revealing ballot choice."""

    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    conn = get_db()
    try:
        voter = conn.execute(
            "SELECT * FROM users WHERE id = ?",
            (user_id,)
        ).fetchone()
    finally:
        conn.close()

    if not voter:
        flash("Voter not found.", "danger")
        return redirect(url_for("admin_voters"))

    # Intentionally do not query election_votes, candidate names, or party names
    # for the admin voter-details page. The admin can see whether a voter voted,
    # but cannot see which candidate/party the voter selected.
    return render_template(
        "admin_voter_details.html",
        voter=voter
    )


# ============================================================
# ADMIN VOTED USERS
# ============================================================

@app.route(
    "/admin_voted"
)
def admin_voted():

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    conn = get_db()

    try:

        voters = conn.execute(
            """
            SELECT DISTINCT
                u.*
            FROM users u
            JOIN election_votes ev
                ON ev.user_id = u.id
            ORDER BY u.id DESC
            """
        ).fetchall()

    finally:

        conn.close()

    return render_template(
        "admin_voted.html",
        voters=voters
    )

# ============================================================
# ADMIN SET GLOBAL VOTING ELIGIBILITY
# ============================================================

@app.route(
    "/admin_set_voting_eligibility",
    methods=["POST"]
)
def admin_set_voting_eligibility():

    if "admin_id" not in session:
        return redirect(
            url_for("admin_login")
        )

    scope = normalize_selection(
        request.form.get("scope")
    )

    state = (
        request.form.get("state") or ""
    ).strip()

    district = (
        request.form.get("district") or ""
    ).strip()

    allowed_scopes = {
        "all_india",
        "state",
        "district"
    }

    if scope not in allowed_scopes:
        flash(
            "Invalid voting eligibility scope.",
            "danger"
        )

        return redirect(
            url_for("admin_dashboard")
        )

    # --------------------------------------------------------
    # ALL INDIA
    # --------------------------------------------------------

    if scope == "all_india":

        state = None
        district = None

    # --------------------------------------------------------
    # STATE
    # --------------------------------------------------------

    elif scope == "state":

        if not state:
            flash(
                "Please select a state.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        if state not in INDIAN_STATES:

            flash(
                "Invalid state selected.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        district = None

    # --------------------------------------------------------
    # DISTRICT
    # --------------------------------------------------------

    elif scope == "district":

        if not state:

            flash(
                "Please select a state.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        if state not in INDIAN_STATES:

            flash(
                "Invalid state selected.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        if not district:

            flash(
                "Please select a district.",
                "danger"
            )

            return redirect(
                url_for("admin_dashboard")
            )

        valid_districts = INDIA_DISTRICTS.get(
            state,
            []
        )

        # Some states in the current dictionary may not yet
        # contain the complete district list. In that case,
        # allow the entered district instead of blocking it.
        if valid_districts:

            normalized_districts = {
                normalize_selection(item): item
                for item in valid_districts
            }

            if normalize_selection(district) not in normalized_districts:

                flash(
                    "Invalid district selected.",
                    "danger"
                )

                return redirect(
                    url_for("admin_dashboard")
                )

            district = normalized_districts[
                normalize_selection(district)
            ]

    conn = get_db()

    try:

        existing = conn.execute(
            """
            SELECT id
            FROM voting_eligibility
            WHERE id = 1
            """
        ).fetchone()

        now = datetime.now().isoformat(
            timespec="seconds"
        )

        if existing:

            conn.execute(
                """
                UPDATE voting_eligibility
                SET
                    scope = ?,
                    state = ?,
                    district = ?,
                    updated_at = ?
                WHERE id = 1
                """,
                (
                    scope,
                    state,
                    district,
                    now
                )
            )

        else:

            conn.execute(
                """
                INSERT INTO voting_eligibility
                (
                    id,
                    scope,
                    state,
                    district,
                    updated_at
                )
                VALUES
                (
                    1,
                    ?,
                    ?,
                    ?,
                    ?
                )
                """,
                (
                    scope,
                    state,
                    district,
                    now
                )
            )

        conn.commit()

        if scope == "all_india":

            message = (
                "Voting eligibility set to All India."
            )

        elif scope == "state":

            message = (
                f"Voting eligibility set to {state}."
            )

        else:

            message = (
                f"Voting eligibility set to "
                f"{district}, {state}."
            )

        flash(
            message,
            "success"
        )

    except sqlite3.Error as e:

        conn.rollback()

        print(
            "Voting eligibility update error:",
            e
        )

        flash(
            "Unable to update voting eligibility.",
            "danger"
        )

    finally:

        conn.close()

    return redirect(
        url_for("admin_dashboard")
    )

# ============================================================
# ADMIN NOT VOTED USERS
# ============================================================

@app.route(
    "/admin_not_voted"
)
def admin_not_voted():

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    conn = get_db()

    try:

        election = conn.execute(
            """
            SELECT *
            FROM elections
            WHERE archived = 0
            ORDER BY id DESC
            LIMIT 1
            """
        ).fetchone()

        if election:

            voters = conn.execute(
                """
                SELECT u.*
                FROM users u
                WHERE NOT EXISTS
                (
                    SELECT 1
                    FROM election_votes ev
                    WHERE ev.user_id = u.id
                    AND ev.election_id = ?
                )
                ORDER BY u.id DESC
                """,
                (
                    election["id"],
                )
            ).fetchall()

        else:

            voters = conn.execute(
                """
                SELECT *
                FROM users
                ORDER BY id DESC
                """
            ).fetchall()

    finally:

        conn.close()

    return render_template(
        "admin_not_voted.html",
        voters=voters,
        election=election
    )


# ============================================================
# ELECTION-SPECIFIC VOTERS
# ============================================================

@app.route(
    "/admin_election_voters/<int:election_id>"
)
def admin_election_voters(
    election_id
):

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    election = get_election(
        election_id
    )

    if not election:

        flash(
            "Election not found.",
            "danger"
        )

        return redirect(
            url_for("admin_dashboard")
        )

    conn = get_db()

    try:

        voters = conn.execute(
            """
            SELECT
                u.*,
                ec.name AS candidate_name,
                ec.party
            FROM election_votes ev
            JOIN users u
                ON u.id = ev.user_id
            JOIN election_candidates ec
                ON ec.id = ev.candidate_id
            WHERE ev.election_id = ?
            ORDER BY ev.id DESC
            """,
            (
                election_id,
            )
        ).fetchall()

    finally:

        conn.close()

    return render_template(
        "admin_voted.html",
        voters=voters,
        election=election
    )


# ============================================================
# PASSWORD REQUESTS
# ============================================================

@app.route(
    "/password_requests"
)
def password_requests():

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    conn = get_db()

    try:

        requests = conn.execute(
            """
            SELECT *
            FROM password_requests
            ORDER BY id DESC
            """
        ).fetchall()

    finally:

        conn.close()

    return render_template(
        "password_requests.html",
        requests=requests
    )


# ============================================================
# APPROVE PASSWORD REQUEST
# ============================================================

@app.route(
    "/approve_password_request/<int:request_id>",
    methods=["POST"]
)
def approve_password_request(
    request_id
):

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    conn = get_db()

    try:

        reset_request = conn.execute(
            """
            SELECT *
            FROM password_requests
            WHERE id = ?
            AND status = 'pending'
            """,
            (
                request_id,
            )
        ).fetchone()

        if not reset_request:

            flash(
                "Password request not found or already processed.",
                "danger"
            )

            return redirect(
                url_for("password_requests")
            )

        user = conn.execute(
            """
            SELECT *
            FROM users
            WHERE LOWER(email) = ?
            AND aadhaar = ?
            AND mobile = ?
            """,
            (
                reset_request["email"].lower(),
                reset_request["aadhaar"],
                reset_request["mobile"]
            )
        ).fetchone()

        if not user:

            flash(
                "Matching voter account was not found.",
                "danger"
            )

            return redirect(
                url_for("password_requests")
            )

        if (
            user["name"].strip().lower()
            !=
            reset_request["name"].strip().lower()
            or
            (
                user["father_name"] or ""
            ).strip().lower()
            !=
            (
                reset_request["father_name"] or ""
            ).strip().lower()
        ):

            flash(
                "Voter identity details do not match.",
                "danger"
            )

            return redirect(
                url_for("password_requests")
            )

        temporary_password = (
            secrets.token_urlsafe(8)
        )

        new_password_hash = (
            generate_password_hash(
                temporary_password
            )
        )

        conn.execute(
            """
            UPDATE users
            SET password = ?
            WHERE id = ?
            """,
            (
                new_password_hash,
                user["id"]
            )
        )

        conn.execute(
            """
            UPDATE password_requests
            SET
                status = 'approved',
                temporary_password = 'GENERATED',
                processed_date = ?
            WHERE id = ?
            """,
            (
                datetime.now().isoformat(),
                request_id
            )
        )

        conn.commit()

        email_sent = send_email(
            reset_request["email"],
            "Online Voting System - New Temporary Password",
            (
                f"Hello {user['name']},\n\n"
                "Your password reset request has been approved.\n\n"
                f"Temporary Password: {temporary_password}\n\n"
                "Please login and change your password "
                "if your system provides that option.\n\n"
                "Online Voting System"
            )
        )

        if email_sent:

            flash(
                "Request approved and temporary password emailed to voter.",
                "success"
            )

        else:

            print(
                "\nTEMPORARY PASSWORD FOR DEVELOPMENT:"
            )

            print(
                temporary_password
            )

            flash(
                "Request approved. SMTP is not configured. Temporary password was printed in the terminal.",
                "warning"
            )

    except Exception as e:

        conn.rollback()

        print(
            "Password approval error:",
            e
        )

        flash(
            "Could not approve password request.",
            "danger"
        )

    finally:

        conn.close()

    return redirect(
        url_for("password_requests")
    )


# ============================================================
# REJECT PASSWORD REQUEST
# ============================================================

@app.route(
    "/reject_password_request/<int:request_id>",
    methods=["POST"]
)
def reject_password_request(
    request_id
):

    if "admin_id" not in session:

        return redirect(
            url_for("admin_login")
        )

    conn = get_db()

    try:

        result = conn.execute(
            """
            UPDATE password_requests
            SET
                status = 'rejected',
                processed_date = ?
            WHERE id = ?
            AND status = 'pending'
            """,
            (
                datetime.now().isoformat(),
                request_id
            )
        )

        if result.rowcount == 0:

            conn.rollback()

            flash(
                "Password request not found or already processed.",
                "danger"
            )

            return redirect(
                url_for("password_requests")
            )

        conn.commit()

    except sqlite3.Error as e:

        conn.rollback()

        print(
            "Password rejection error:",
            e
        )

        flash(
            "Unable to reject password request.",
            "danger"
        )

        return redirect(
            url_for("password_requests")
        )

    finally:

        conn.close()

    flash(
        "Password reset request rejected.",
        "success"
    )

    return redirect(
        url_for("password_requests")
    )


# ============================================================
# LEGACY BLOCKCHAIN PAGE
# ============================================================

@app.route(
    "/blockchain"
)
def blockchain():
    """Show the blockchain for a selected election, including archived ones.

    By default, show the most recently created election. An admin can select
    any retained election with /blockchain?election_id=<id>.
    """
    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    requested_id = request.args.get("election_id", type=int)
    conn = get_db()
    try:
        elections = conn.execute(
            "SELECT id, name, status, archived FROM elections ORDER BY id DESC"
        ).fetchall()

        election = None
        if requested_id is not None:
            election = conn.execute(
                "SELECT * FROM elections WHERE id = ?",
                (requested_id,)
            ).fetchone()

        # If the requested ID is invalid or absent, default to the newest
        # election, without excluding archived elections.
        if election is None and elections:
            election = conn.execute(
                "SELECT * FROM elections ORDER BY id DESC LIMIT 1"
            ).fetchone()

        blocks = []
        if election:
            blocks = conn.execute(
                "SELECT * FROM election_blockchain WHERE election_id = ? ORDER BY id DESC",
                (election["id"],)
            ).fetchall()
    finally:
        conn.close()

    if not election:
        return render_template(
            "blockchain.html",
            election=None,
            elections=[],
            selected_election_id=None,
            blocks=[],
            blockchain_valid=True,
            blockchain_message="No elections found. Create an election to start using the election blockchain."
        )

    valid, message = verify_election_blockchain(election["id"])
    if not blocks:
        message = "No blockchain blocks are stored for this election yet."

    return render_template(
        "blockchain.html",
        election=election,
        elections=elections,
        selected_election_id=election["id"],
        blocks=blocks,
        blockchain_valid=valid,
        blockchain_message=message
    )


# ============================================================
# BLOCKCHAIN STATUS
# ============================================================

@app.route(
    "/blockchain_status"
)
def blockchain_status():
    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    requested_id = request.args.get("election_id", type=int)
    conn = get_db()
    try:
        elections = conn.execute(
            "SELECT id, name, status, archived FROM elections ORDER BY id DESC"
        ).fetchall()

        election = None
        if requested_id is not None:
            election = conn.execute(
                "SELECT * FROM elections WHERE id = ?",
                (requested_id,)
            ).fetchone()
        if election is None and elections:
            election = conn.execute(
                "SELECT * FROM elections ORDER BY id DESC LIMIT 1"
            ).fetchone()
    finally:
        conn.close()

    if not election:
        return render_template(
            "blockchain_status.html",
            valid=True,
            message="No election blockchain found.",
            election=None,
            elections=[],
            selected_election_id=None
        )

    valid, message = verify_election_blockchain(election["id"])
    return render_template(
        "blockchain_status.html",
        valid=valid,
        message=message,
        election=election,
        elections=elections,
        selected_election_id=election["id"]
    )


# ============================================================
# USER LOGOUT
# ============================================================

@app.route(
    "/logout"
)
def logout():

    session.clear()

    flash(
        "You have been logged out.",
        "success"
    )

    return redirect(
        url_for("index")
    )


# ============================================================
# ADMIN LOGOUT
# ============================================================

@app.route(
    "/admin_logout"
)
def admin_logout():

    session.clear()

    flash(
        "Administrator logged out successfully.",
        "success"
    )

    return redirect(
        url_for("index")
    )


# ============================================================
# 413 FILE TOO LARGE
# ============================================================

@app.errorhandler(413)
def file_too_large(error):

    flash(
        "Uploaded photo is too large. Maximum size is 5 MB.",
        "danger"
    )

    return redirect(
        url_for("register")
    )


# ============================================================
# 500 ERROR
# ============================================================

@app.errorhandler(500)
def internal_error(error):

    print(
        "Internal server error:",
        error
    )

    return """
    <!DOCTYPE html>
    <html>

    <head>

        <title>Server Error</title>

        <style>

            body {
                font-family: Arial, sans-serif;
                background: #f8fafc;
                text-align: center;
                padding: 60px;
            }

            .box {
                background: white;
                max-width: 600px;
                margin: auto;
                padding: 30px;
                border-radius: 15px;
                box-shadow: 0 10px 30px rgba(0,0,0,.1);
            }

            h1 {
                color: #b91c1c;
            }

        </style>

    </head>

    <body>

        <div class="box">

            <h1>
                🇮🇳 Internal Server Error
            </h1>

            <p>
                Something went wrong on the server.
            </p>

            <p>
                Please check the Flask terminal
                for the exact error.
            </p>

        </div>

    </body>

    </html>
    """, 500


# ============================================================
# START APPLICATION
# ============================================================

if __name__ == "__main__":

    # ========================================================
    # DATABASE INITIALIZATION
    # ========================================================

    init_db()

    print()

    print(
        "======================================"
    )

    print(
        "🇮🇳 ONLINE VOTING SYSTEM"
    )

    print(
        "======================================"
    )

    print(
        f"Admin Username: "
        f"{ADMIN_USERNAME}"
    )

    print(
        f"Admin Password: "
        f"{ADMIN_DEFAULT_PASSWORD}"
    )

    print(
        f"Database: "
        f"{DATABASE}"
    )

    print(
        "Server: "
        "http://127.0.0.1:5000"
    )

    print(
        "Network: "
        "http://192.168.1.76:5000"
    )

    print(
        "======================================"
    )

    print()

    if not OPENCV_AVAILABLE:

        print(
            "⚠️ WARNING: OpenCV is not installed."
        )

        print(
            "Run:"
        )

        print(
            "pip install opencv-python"
        )

        print()

    app.run(
        host="0.0.0.0",
        port=5000,
        debug=True
    )