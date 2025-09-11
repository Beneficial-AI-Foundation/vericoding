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


def get_cheat_message(cheats: List[Tuple[str, str]], is_final: bool = False) -> str:
    """Generate a user-friendly message about detected cheats.
    
    Args:
        cheats: List of (pattern, description) tuples from check_for_cheats
        is_final: Whether this is the final iteration (determines message tone)
        
    Returns:
        Formatted error message
    """
    if not cheats:
        return ""
    
    if is_final:
        # Final iteration - this is an error
        if len(cheats) == 1:
            return f"FINAL VERIFICATION FAILED: Your response included verification bypass: {cheats[0][1]}. This is not allowed for final answers."
        cheat_descriptions = [desc for _, desc in cheats]
        return f"FINAL VERIFICATION FAILED: Your response included verification bypasses: {', '.join(cheat_descriptions)}. These are not allowed for final answers."
    else:
        # Intermediate iteration - this is a warning
        if len(cheats) == 1:
            return f"WARNING: Your response included verification bypass: {cheats[0][1]}. This must be removed in subsequent iterations for final success."
        cheat_descriptions = [desc for _, desc in cheats]
        return f"WARNING: Your response included verification bypasses: {', '.join(cheat_descriptions)}. These must be removed in subsequent iterations for final success."


def has_final_failure_cheats(code: str) -> bool:
    """Check if code has cheats that would cause final verification failure.
    
    This is used to determine if verification should be considered failed
    even if lake build succeeds.
    
    Args:
        code: The Lean code to check
        
    Returns:
        True if code has verification bypasses that make it invalid
    """
    return has_cheats(code)