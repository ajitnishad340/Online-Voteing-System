
# ============================================================
# ONLINE VOTING SYSTEM - BLOCKCHAIN MODULE
# File: blockchain.py
# ============================================================

import hashlib
import json
from datetime import datetime, timezone


GENESIS_HASH = "0" * 64


def calculate_block_hash(
    block_id,
    voter_hash,
    candidate_name,
    timestamp,
    previous_hash
):
    """
    Generate a SHA-256 hash for a voting record.
    """

    block_data = (
        f"{block_id}|"
        f"{voter_hash}|"
        f"{candidate_name}|"
        f"{timestamp}|"
        f"{previous_hash}"
    )

    return hashlib.sha256(
        block_data.encode("utf-8")
    ).hexdigest()


def create_block(
    block_id,
    voter_hash,
    candidate_name,
    previous_hash=GENESIS_HASH,
    timestamp=None
):
    """
    Create a blockchain record for a vote.

    This function does not save anything to the database.
    """

    if timestamp is None:
        timestamp = datetime.now(
            timezone.utc
        ).isoformat()

    block = {
        "id": block_id,
        "voter_hash": voter_hash,
        "candidate_name": candidate_name,
        "timestamp": timestamp,
        "previous_hash": previous_hash
    }

    block["block_hash"] = calculate_block_hash(
        block_id,
        voter_hash,
        candidate_name,
        timestamp,
        previous_hash
    )

    return block


def verify_chain(blocks):
    """
    Verify the order and hashes of blockchain records.

    Each block must contain:
    id, voter_hash, candidate_name, timestamp,
    previous_hash, block_hash
    """

    previous_hash = GENESIS_HASH

    for block in blocks:
        block_id = block["id"]
        voter_hash = block["voter_hash"]
        candidate_name = block["candidate_name"]
        timestamp = block["timestamp"]
        stored_previous_hash = block["previous_hash"]
        stored_hash = block["block_hash"]

        if stored_previous_hash != previous_hash:
            return (
                False,
                f"Invalid previous hash at block {block_id}."
            )

        expected_hash = calculate_block_hash(
            block_id,
            voter_hash,
            candidate_name,
            timestamp,
            stored_previous_hash
        )

        if stored_hash != expected_hash:
            return (
                False,
                f"Invalid block hash at block {block_id}."
            )

        previous_hash = stored_hash

    return True, "Blockchain is valid."


def export_chain(blocks):
    """
    Convert blockchain records into formatted JSON.
    Useful for viewing or exporting records.
    """

    return json.dumps(
        [dict(block) for block in blocks],
        indent=4,
        ensure_ascii=False
    )
