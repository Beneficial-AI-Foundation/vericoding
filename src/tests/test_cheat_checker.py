"""Tests for cheat detection utilities."""

import pytest
from vericoding.processing.cheat_checker import (
    check_for_cheats,
    has_cheats,
    get_cheat_message,
    has_final_failure_cheats,
)


class TestLeanCheatDetection:
    """Test cheat detection for Lean language."""

    def test_detects_sorry_outside_preamble(self):
        """Should detect sorry when it's outside vc-preamble sections."""
        code = """
theorem test : True := by
  sorry
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r'\bsorry\b'
        assert "sorry" in cheats[0][1]

    def test_ignores_sorry_inside_preamble(self):
        """Should ignore sorry when it's inside vc-preamble sections."""
        code = """
<vc-preamble>
axiom test_axiom : True
lemma helper : True := sorry
</vc-preamble>

theorem main : True := by
  exact test_axiom
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0

    def test_mixed_sorry_locations(self):
        """Should detect sorry outside preamble but ignore sorry inside preamble."""
        code = """
<vc-preamble>
axiom test_axiom : True
lemma helper : True := sorry  -- This should be ignored
</vc-preamble>

theorem main : True := by
  sorry  -- This should be detected
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r'\bsorry\b'

    def test_multiple_preamble_sections(self):
        """Should handle multiple vc-preamble sections correctly."""
        code = """
<vc-preamble>
lemma helper1 : True := sorry  -- Ignored
</vc-preamble>

theorem test1 : True := by
  sorry  -- Detected

<vc-preamble>
lemma helper2 : True := sorry  -- Ignored
</vc-preamble>

theorem test2 : True := by
  sorry  -- Detected
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1  # Only one entry per pattern type
        assert cheats[0][0] == r'\bsorry\b'

    def test_detects_admit_outside_preamble(self):
        """Should detect admit when it's outside vc-preamble sections."""
        code = """
theorem test : True := by
  admit
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r'\badmit\b'
        assert "admit" in cheats[0][1]

    def test_ignores_admit_inside_preamble(self):
        """Should ignore admit when it's inside vc-preamble sections."""
        code = """
<vc-preamble>
lemma helper : True := admit
</vc-preamble>

theorem main : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0

    def test_detects_axiom_outside_preamble(self):
        """Should detect axiom when it's outside vc-preamble sections."""
        code = """
axiom bad_axiom : False

theorem test : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r'\baxiom\b'
        assert "axiom" in cheats[0][1]

    def test_ignores_axiom_inside_preamble(self):
        """Should ignore axiom when it's inside vc-preamble sections."""
        code = """
<vc-preamble>
axiom test_axiom : True
</vc-preamble>

theorem main : True := by
  exact test_axiom
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0

    def test_detects_unsafe_outside_preamble(self):
        """Should detect unsafe when it's outside vc-preamble sections."""
        code = """
unsafe def bad_function : Nat := 42

theorem test : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r'\bunsafe\b'
        assert "unsafe" in cheats[0][1]

    def test_detects_unchecked_cast_outside_preamble(self):
        """Should detect Unchecked.cast when it's outside vc-preamble sections."""
        code = """
def bad_cast : Nat := Unchecked.cast 42

theorem test : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r'\bUnchecked\.cast\b'
        assert "type checking" in cheats[0][1]

    def test_detects_extern_outside_preamble(self):
        """Should detect @[extern] when it's outside vc-preamble sections."""
        code = """
@[extern "bad_function"]
def bad_function : Nat := 42

theorem test : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r'@\[extern'
        assert "extern" in cheats[0][1]

    def test_multiple_cheat_types_mixed_locations(self):
        """Should detect multiple types of cheats, respecting preamble exclusions."""
        code = """
<vc-preamble>
axiom helper_axiom : True
lemma helper : True := sorry
unsafe def helper_unsafe : Nat := 42
</vc-preamble>

theorem main : True := by
  sorry  -- Should be detected

axiom bad_axiom : False  -- Should be detected

def test : Nat := Unchecked.cast 42  -- Should be detected
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 3  # sorry, axiom, Unchecked.cast
        cheat_patterns = {cheat[0] for cheat in cheats}
        assert r'\bsorry\b' in cheat_patterns
        assert r'\baxiom\b' in cheat_patterns
        assert r'\bUnchecked\.cast\b' in cheat_patterns

    def test_no_cheats_detected(self):
        """Should detect no cheats in clean code."""
        code = """
<vc-preamble>
axiom helper : True
lemma test_helper : True := sorry
</vc-preamble>

theorem main : True := by
  exact helper
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0


class TestDafnyCheatDetection:
    """Test cheat detection for Dafny language."""

    def test_detects_axiom_attribute(self):
        """Should detect {:axiom} attribute in Dafny."""
        code = """
lemma {:axiom} BadLemma()
  ensures false
"""
        cheats = check_for_cheats(code, "dafny")
        assert len(cheats) == 1
        assert cheats[0][0] == r'\{:axiom\}'
        assert "axiom" in cheats[0][1]

    def test_ignores_axiom_inside_preamble(self):
        """Should ignore {:axiom} when it's inside vc-preamble sections."""
        code = """
<vc-preamble>
lemma {:axiom} HelperAxiom()
  ensures true
</vc-preamble>

lemma MainLemma()
  ensures HelperAxiom()
{
  // proof using helper axiom
}
"""
        cheats = check_for_cheats(code, "dafny")
        assert len(cheats) == 0

    def test_detects_axiom_outside_preamble(self):
        """Should detect {:axiom} when it's outside vc-preamble sections."""
        code = """
<vc-preamble>
lemma {:axiom} HelperAxiom()
  ensures true
</vc-preamble>

lemma {:axiom} BadLemma()  // This should be detected
  ensures false
"""
        cheats = check_for_cheats(code, "dafny")
        assert len(cheats) == 1
        assert cheats[0][0] == r'\{:axiom\}'

    def test_multiple_preamble_sections_dafny(self):
        """Should handle multiple vc-preamble sections in Dafny."""
        code = """
<vc-preamble>
lemma {:axiom} Helper1()
  ensures true
</vc-preamble>

lemma {:axiom} BadLemma1()  // Detected
  ensures false

<vc-preamble>
lemma {:axiom} Helper2()
  ensures true
</vc-preamble>

lemma {:axiom} BadLemma2()  // Detected
  ensures false
"""
        cheats = check_for_cheats(code, "dafny")
        assert len(cheats) == 1  # Only one entry per pattern type

    def test_no_cheats_in_clean_dafny(self):
        """Should detect no cheats in clean Dafny code."""
        code = """
lemma GoodLemma()
  ensures true
{
  // proof here
}
"""
        cheats = check_for_cheats(code, "dafny")
        assert len(cheats) == 0

    def test_no_cheats_with_preamble_only(self):
        """Should detect no cheats when axioms are only in preamble."""
        code = """
<vc-preamble>
lemma {:axiom} Helper1()
  ensures true

lemma {:axiom} Helper2()
  ensures false
</vc-preamble>

lemma MainLemma()
  ensures Helper1()
{
  // valid proof
}
"""
        cheats = check_for_cheats(code, "dafny")
        assert len(cheats) == 0


class TestVerusCheatDetection:
    """Test cheat detection for Verus language."""

    def test_no_cheats_detected_for_verus(self):
        """Verus uses --no-cheating flag, so no string-based detection."""
        code = """
fn test_function() -> bool {
    true
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 0


class TestCheatCheckerHelpers:
    """Test helper functions for cheat checking."""

    def test_has_cheats_true(self):
        """Should return True when cheats are detected."""
        code = "theorem test : True := sorry"
        assert has_cheats(code, "lean") is True

    def test_has_cheats_false(self):
        """Should return False when no cheats are detected."""
        code = """
<vc-preamble>
lemma helper : True := sorry
</vc-preamble>

theorem test : True := by exact helper
"""
        assert has_cheats(code, "lean") is False

    def test_has_final_failure_cheats(self):
        """Should return True when code has cheats that cause final failure."""
        code = "theorem test : True := sorry"
        assert has_final_failure_cheats(code, "lean") is True

    def test_get_cheat_message_single_warning(self):
        """Should generate warning message for single cheat."""
        cheats = [(r'\bsorry\b', "uses 'sorry' to bypass verification")]
        message = get_cheat_message(cheats, is_final=False)
        assert "WARNING" in message
        assert "sorry" in message
        assert "subsequent iterations" in message

    def test_get_cheat_message_multiple_warnings(self):
        """Should generate warning message for multiple cheats."""
        cheats = [
            (r'\bsorry\b', "uses 'sorry' to bypass verification"),
            (r'\badmit\b', "uses 'admit' to bypass verification"),
        ]
        message = get_cheat_message(cheats, is_final=False)
        assert "WARNING" in message
        assert "sorry" in message
        assert "admit" in message

    def test_get_cheat_message_single_final_error(self):
        """Should generate error message for single cheat in final iteration."""
        cheats = [(r'\bsorry\b', "uses 'sorry' to bypass verification")]
        message = get_cheat_message(cheats, is_final=True)
        assert "FINAL VERIFICATION FAILED" in message
        assert "sorry" in message
        assert "not allowed for final" in message

    def test_get_cheat_message_multiple_final_errors(self):
        """Should generate error message for multiple cheats in final iteration."""
        cheats = [
            (r'\bsorry\b', "uses 'sorry' to bypass verification"),
            (r'\badmit\b', "uses 'admit' to bypass verification"),
        ]
        message = get_cheat_message(cheats, is_final=True)
        assert "FINAL VERIFICATION FAILED" in message
        assert "sorry" in message
        assert "admit" in message

    def test_get_cheat_message_empty(self):
        """Should return empty string when no cheats."""
        message = get_cheat_message([], is_final=False)
        assert message == ""

    def test_unsupported_language_error(self):
        """Should raise ValueError for unsupported languages."""
        with pytest.raises(ValueError, match="Unsupported language"):
            check_for_cheats("code", "unsupported")


class TestPreambleEdgeCases:
    """Test edge cases for vc-preamble handling."""

    def test_nested_preamble_tags(self):
        """Should handle nested preamble tags correctly."""
        code = """
<vc-preamble>
axiom outer : True
<vc-preamble>
lemma inner : True := sorry
</vc-preamble>
</vc-preamble>

theorem test : True := by
  sorry
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1  # Only the sorry outside preamble

    def test_incomplete_preamble_tags(self):
        """Should handle incomplete preamble tags gracefully."""
        code = """
<vc-preamble>
lemma incomplete : True := sorry
-- Missing closing tag

theorem test : True := by
  sorry
"""
        # The regex should not match incomplete tags, so both sorries should be detected
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1  # Only detects pattern once

    def test_empty_preamble_section(self):
        """Should handle empty preamble sections correctly."""
        code = """
<vc-preamble>
</vc-preamble>

theorem test : True := by
  sorry
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1

    def test_preamble_with_multiline_content(self):
        """Should handle multiline preamble content correctly."""
        code = """
<vc-preamble>
axiom test_axiom : True

lemma helper_lemma : True := by
  sorry
  
def helper_function : Nat := 42
</vc-preamble>

theorem main : True := by
  sorry  -- This should be detected
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1