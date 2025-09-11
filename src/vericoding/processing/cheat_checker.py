"""Cheat detection utilities for Lean verification."""

import re
from typing import List, Tuple


def check_for_cheats(code: str) -> List[Tuple[str, str]]:
    """Check for verification bypasses and cheating patterns in Lean code.
    
    Args:
        code: The Lean code to check
        
    Returns:
        List of (pattern, description) tuples for detected cheats
    """
    cheat_patterns = [
        (r'\bsorry\b', "uses 'sorry' to bypass verification"),
        (r'\baxiom\b', "introduces axioms bypassing verification"), 
        (r'\bunsafe\b', "uses unsafe operations"),
        (r'\bUnchecked\.cast\b', "bypasses type checking"),
        (r'\bpartial\b\s+def\b', "uses partial def without termination proof"),
        (r'@\[extern\]', "uses extern functions bypassing verification"),
    ]
    
    detected_cheats = []
    
    for pattern, description in cheat_patterns:
        if re.search(pattern, code):
            detected_cheats.append((pattern, description))
    
    return detected_cheats


def has_cheats(code: str) -> bool:
    """Quick check if code contains any verification cheats.
    
    Args:
        code: The Lean code to check
        
    Returns:
        True if cheats are detected, False otherwise
    """
    return len(check_for_cheats(code)) > 0


def get_cheat_message(cheats: List[Tuple[str, str]]) -> str:
    """Generate a user-friendly message about detected cheats.
    
    Args:
        cheats: List of (pattern, description) tuples from check_for_cheats
        
    Returns:
        Formatted error message
    """
    if not cheats:
        return ""
    
    if len(cheats) == 1:
        return f"Your response included verification bypass: {cheats[0][1]}. This is not allowed for final answers."
    
    cheat_descriptions = [desc for _, desc in cheats]
    return f"Your response included verification bypasses: {', '.join(cheat_descriptions)}. These are not allowed for final answers."