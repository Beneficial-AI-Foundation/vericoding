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

    def test_ignores_sorry_outside_editable_sections(self):
        """Should ignore sorry when it's outside editable sections."""
        code = """
theorem test : True := by
  sorry  -- This should be ignored (not in editable section)
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0

    def test_detects_sorry_inside_vc_definitions(self):
        """Should detect sorry when it's inside vc-definitions sections."""
        code = """
<vc-definitions>
def factorial (n : Nat) : Nat := sorry
</vc-definitions>

theorem main : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r"\bsorry\b"
        assert "sorry" in cheats[0][1]

    def test_detects_sorry_inside_vc_theorems(self):
        """Should detect sorry when it's inside vc-theorems sections."""
        code = """
<vc-theorems>
theorem test : True := by
  sorry  -- This should be detected
</vc-theorems>
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r"\bsorry\b"

    def test_mixed_sorry_locations(self):
        """Should detect sorry inside editable sections but ignore sorry outside."""
        code = """
axiom test_axiom : True
lemma helper : True := sorry  -- This should be ignored (not in editable section)

<vc-theorems>
theorem main : True := by
  sorry  -- This should be detected
</vc-theorems>
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r"\bsorry\b"

    def test_multiple_editable_sections(self):
        """Should handle multiple editable sections correctly."""
        code = """
<vc-definitions>
def helper1 : Nat := sorry  -- Detected
</vc-definitions>

theorem test1 : True := by
  sorry  -- Ignored (not in editable section)

<vc-theorems>
theorem helper2 : True := by sorry  -- Detected
</vc-theorems>

theorem test2 : True := by
  sorry  -- Ignored (not in editable section)
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1  # Only one entry per pattern type
        assert cheats[0][0] == r"\bsorry\b"

    def test_ignores_admit_outside_editable_sections(self):
        """Should ignore admit when it's outside editable sections."""
        code = """
theorem test : True := by
  admit  -- Ignored (not in editable section)
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0

    def test_detects_admit_inside_editable_sections(self):
        """Should detect admit when it's inside editable sections."""
        code = """
<vc-helpers>
lemma helper : True := admit  -- Detected
</vc-helpers>

theorem main : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r"\badmit\b"
        assert "admit" in cheats[0][1]

    def test_ignores_axiom_outside_editable_sections(self):
        """Should ignore axiom when it's outside editable sections."""
        code = """
axiom bad_axiom : False  -- Ignored (not in editable section)

theorem test : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0

    def test_detects_axiom_inside_editable_sections(self):
        """Should detect axiom when it's inside editable sections."""
        code = """
<vc-definitions>
axiom test_axiom : True  -- Detected
</vc-definitions>

theorem main : True := by
  exact test_axiom
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r"\baxiom\b"
        assert "axiom" in cheats[0][1]

    def test_ignores_unsafe_outside_editable_sections(self):
        """Should ignore unsafe when it's outside editable sections."""
        code = """
unsafe def bad_function : Nat := 42  -- Ignored (not in editable section)

theorem test : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0

    def test_detects_unsafe_inside_editable_sections(self):
        """Should detect unsafe when it's inside editable sections."""
        code = """
<vc-definitions>
unsafe def bad_function : Nat := 42  -- Detected
</vc-definitions>

theorem test : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r"\bunsafe\b"
        assert "unsafe" in cheats[0][1]

    def test_ignores_unchecked_cast_outside_editable_sections(self):
        """Should ignore Unchecked.cast when it's outside editable sections."""
        code = """
def bad_cast : Nat := Unchecked.cast 42  -- Ignored (not in editable section)

theorem test : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0

    def test_detects_unchecked_cast_inside_editable_sections(self):
        """Should detect Unchecked.cast when it's inside editable sections."""
        code = """
<vc-helpers>
def bad_cast : Nat := Unchecked.cast 42  -- Detected
</vc-helpers>

theorem test : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r"\bUnchecked\.cast\b"
        assert "type checking" in cheats[0][1]

    def test_ignores_extern_outside_editable_sections(self):
        """Should ignore @[extern] when it's outside editable sections."""
        code = """
@[extern "bad_function"]  -- Ignored (not in editable section)
def bad_function : Nat := 42

theorem test : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0

    def test_detects_extern_inside_editable_sections(self):
        """Should detect @[extern] when it's inside editable sections."""
        code = """
<vc-theorems>
@[extern "bad_function"]  -- Detected
def bad_function : Nat := 42
</vc-theorems>

theorem test : True := by
  exact True.intro
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 1
        assert cheats[0][0] == r"@\[extern"
        assert "extern" in cheats[0][1]

    def test_multiple_cheat_types_mixed_locations(self):
        """Should detect multiple types of cheats, respecting editable section rules."""
        code = """
axiom helper_axiom : True  -- Ignored (not in editable section)
lemma helper : True := sorry  -- Ignored (not in editable section)
unsafe def helper_unsafe : Nat := 42  -- Ignored (not in editable section)

<vc-theorems>
theorem main : True := by
  sorry  -- Should be detected
</vc-theorems>

<vc-definitions>
axiom bad_axiom : False  -- Should be detected
</vc-definitions>

<vc-helpers>
def test : Nat := Unchecked.cast 42  -- Should be detected
</vc-helpers>
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 3  # sorry, axiom, Unchecked.cast
        cheat_patterns = {cheat[0] for cheat in cheats}
        assert r"\bsorry\b" in cheat_patterns
        assert r"\baxiom\b" in cheat_patterns
        assert r"\bUnchecked\.cast\b" in cheat_patterns

    def test_no_cheats_detected(self):
        """Should detect no cheats in clean code."""
        code = """
axiom helper : True  -- Ignored (not in editable section)
lemma test_helper : True := sorry  -- Ignored (not in editable section)

<vc-helpers>
lemma clean_helper : True := by trivial  -- No cheats here
</vc-helpers>

theorem main : True := by
  exact helper
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0


class TestDafnyCheatDetection:
    """Test cheat detection for Dafny language."""

    def test_ignores_axiom_attribute_outside_editable_sections(self):
        """Should ignore {:axiom} attribute when outside editable sections."""
        code = """
lemma {:axiom} BadLemma()  // Ignored (not in editable section)
  ensures false
"""
        cheats = check_for_cheats(code, "dafny")
        assert len(cheats) == 0

    def test_detects_axiom_inside_vc_code(self):
        """Should detect {:axiom} when it's inside vc-code sections."""
        code = """
method Test() {
    <vc-code>
    lemma {:axiom} BadLemma()  // Detected
      ensures false
    </vc-code>
}
"""
        cheats = check_for_cheats(code, "dafny")
        assert len(cheats) == 1
        assert cheats[0][0] == r"\{:axiom\}"
        assert "axiom" in cheats[0][1]

    def test_detects_axiom_inside_vc_helpers(self):
        """Should detect {:axiom} when it's inside vc-helpers sections."""
        code = """
<vc-helpers>
lemma {:axiom} HelperAxiom()  // Detected
  ensures true
</vc-helpers>

lemma MainLemma()
  ensures HelperAxiom()
{
  // proof using helper axiom
}
"""
        cheats = check_for_cheats(code, "dafny")
        assert len(cheats) == 1
        assert cheats[0][0] == r"\{:axiom\}"

    def test_multiple_editable_sections_dafny(self):
        """Should handle multiple editable sections in Dafny."""
        code = """
<vc-helpers>
lemma {:axiom} Helper1()  // Detected
  ensures true
</vc-helpers>

lemma {:axiom} BadLemma1()  // Ignored (not in editable section)
  ensures false

<vc-code>
lemma {:axiom} Helper2()  // Detected
  ensures true
</vc-code>

lemma {:axiom} BadLemma2()  // Ignored (not in editable section)
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

    def test_no_cheats_when_outside_editable_sections(self):
        """Should detect no cheats when axioms are only outside editable sections."""
        code = """
lemma {:axiom} Helper1()  // Ignored (not in editable section)
  ensures true

lemma {:axiom} Helper2()  // Ignored (not in editable section)
  ensures false

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

    def test_ignores_assume_outside_editable_sections(self):
        """Should ignore 'assume' when it's outside editable sections."""
        code = """
fn test_function(x: u32) -> u32 {
    assume(x > 0);  // Ignored (not in editable section)
    x + 1
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 0

    def test_ignores_assume_in_word_outside_editable_sections(self):
        """Should ignore 'assume' even when part of a bigger word when outside editable sections."""
        code = """
fn test_function() {
    let assumed_value = true;  // Ignored (not in editable section)
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 0

    def test_detects_assume_inside_editable_sections(self):
        """Should detect 'assume' when it's inside editable sections."""
        code = """
<vc-code>
fn helper_with_precondition(x: u32) -> u32 {
    assume(x > 0);  // Detected
    x + 1
}
</vc-code>

fn main_function() -> u32 {
    helper_with_precondition(5)
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 1
        assert cheats[0][0] == r"assume"
        assert "assume" in cheats[0][1]

    def test_ignores_admit_outside_editable_sections(self):
        """Should ignore 'admit' when it's outside editable sections."""
        code = """
fn test_function() -> bool
    ensures true
{
    admit();  // Ignored (not in editable section)
    true
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 0

    def test_detects_admit_inside_editable_sections(self):
        """Should detect 'admit' when it's inside editable sections."""
        code = """
<vc-helpers>
fn helper_with_admit() -> bool {
    admit();  // Detected
    true
}
</vc-helpers>

fn main_function() -> bool {
    helper_with_admit()
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 1
        assert cheats[0][0] == r"\badmit\b"
        assert "admit" in cheats[0][1]

    def test_ignores_external_body_outside_editable_sections(self):
        """Should ignore '#[verifier::external_body]' when it's outside editable sections."""
        code = """
#[verifier::external_body]  // Ignored (not in editable section)
fn bad_function() -> bool {
    true
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 0

    def test_detects_external_body_inside_editable_sections(self):
        """Should detect '#[verifier::external_body]' when it's inside editable sections."""
        code = """
<vc-code>
#[verifier::external_body]  // Detected
fn helper_function() -> bool {
    true
}
</vc-code>

fn main_function() -> bool {
    helper_function()
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 1
        assert cheats[0][0] == r"#\[verifier::external"
        assert "verifier external" in cheats[0][1]

    def test_ignores_external_wildcard_outside_editable_sections(self):
        """Should ignore '#[verifier::external*' patterns when outside editable sections."""
        code = """
#[verifier::external_fn_specification]  // Ignored (not in editable section)
fn bad_function() -> bool {
    true
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 0

    def test_detects_external_wildcard_inside_editable_sections(self):
        """Should detect '#[verifier::external*' patterns when inside editable sections."""
        code = """
<vc-helpers>
#[verifier::external_fn_specification]  // Detected
fn helper_function() -> bool {
    true
}
</vc-helpers>

fn main_function() -> bool {
    helper_function()
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 1
        assert cheats[0][0] == r"#\[verifier::external"
        assert "verifier external" in cheats[0][1]

    def test_ignores_exec_allows_no_decreases_outside_editable_sections(self):
        """Should ignore '#[verifier::exec_allows_no_decreases_clause]' when outside editable sections."""
        code = """
#[verifier::exec_allows_no_decreases_clause]  // Ignored (not in editable section)
fn bad_recursive_function(n: u32) -> u32 {
    if n == 0 { 0 } else { bad_recursive_function(n - 1) }
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 0

    def test_detects_exec_allows_no_decreases_inside_editable_sections(self):
        """Should detect '#[verifier::exec_allows_no_decreases_clause]' when inside editable sections."""
        code = """
<vc-code>
#[verifier::exec_allows_no_decreases_clause]  // Detected
fn helper_recursive_function(n: u32) -> u32 {
    if n == 0 { 0 } else { helper_recursive_function(n - 1) }
}
</vc-code>

fn main_function() -> u32 {
    helper_recursive_function(5)
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 1
        assert cheats[0][0] == r"#\[verifier::exec_allows_no_decreases_clause\]"
        assert "exec_allows_no_decreases_clause" in cheats[0][1]

    def test_multiple_cheat_types_mixed_locations_verus(self):
        """Should detect multiple types of cheats, respecting editable section rules."""
        code = """
fn helper_with_precondition(x: u32) -> u32 {  // Ignored (not in editable section)
    assume(x > 0);
    x + 1
}

#[verifier::external_body]  // Ignored (not in editable section)
fn helper_external() -> bool {
    true
}

fn main_function() -> bool {  // Ignored (not in editable section)
    assume(true);
    admit();
    true
}

<vc-code>
fn bad1() -> bool {
    assume(true);  // Should be detected
    admit();      // Should be detected
    true
}
</vc-code>

<vc-helpers>
#[verifier::external_body]  // Should be detected
fn bad_function() -> bool {
    true
}
</vc-helpers>
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 3  # assume, admit, external
        cheat_patterns = {cheat[0] for cheat in cheats}
        assert r"assume" in cheat_patterns
        assert r"\badmit\b" in cheat_patterns
        assert r"#\[verifier::external" in cheat_patterns

    def test_multiple_editable_sections_verus(self):
        """Should handle multiple editable sections in Verus."""
        code = """
<vc-code>
fn helper1() {
    assume(true);  // Detected
}
</vc-code>

fn bad1() {  // Ignored (not in editable section)
    assume(false);
}

<vc-helpers>
fn helper2() {
    admit();  // Detected
}
</vc-helpers>

fn bad2() {  // Ignored (not in editable section)
    admit();
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 2  # assume and admit (one entry each)
        cheat_patterns = {cheat[0] for cheat in cheats}
        assert r"assume" in cheat_patterns
        assert r"\badmit\b" in cheat_patterns

    def test_no_cheats_in_clean_verus(self):
        """Should detect no cheats in clean Verus code."""
        code = """
fn test_function(x: u32) -> u32
    requires x > 0
    ensures result > x
{
    x + 1
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 0

    def test_no_cheats_when_outside_editable_sections_verus(self):
        """Should detect no cheats when all bypasses are only outside editable sections."""
        code = """
fn helper_precondition(x: u32) -> u32 {  // Ignored (not in editable section)
    assume(x > 0);
    x + 1
}

#[verifier::external_body]  // Ignored (not in editable section)
fn helper_external() -> bool {
    true
}

#[verifier::exec_allows_no_decreases_clause]  // Ignored (not in editable section)
fn helper_recursive(n: u32) -> u32 {
    if n == 0 { 0 } else { helper_recursive(n - 1) }
}

fn main_function() -> bool
    ensures result == true
{
    helper_external() && helper_precondition(5) > 0
}
"""
        cheats = check_for_cheats(code, "verus")
        assert len(cheats) == 0


class TestCheatCheckerHelpers:
    """Test helper functions for cheat checking."""

    def test_has_cheats_true(self):
        """Should return True when cheats are detected."""
        code = "<vc-theorems>\ntheorem test : True := sorry\n</vc-theorems>"
        assert has_cheats(code, "lean") is True

    def test_has_cheats_false(self):
        """Should return False when no cheats are detected."""
        code = """
lemma helper : True := sorry  -- Ignored (not in editable section)

<vc-helpers>
lemma clean_helper : True := by trivial  -- No cheats here
</vc-helpers>

theorem test : True := by exact helper
"""
        assert has_cheats(code, "lean") is False

    def test_has_final_failure_cheats(self):
        """Should return True when code has cheats that cause final failure."""
        code = "<vc-definitions>\ndef test : Nat := sorry\n</vc-definitions>"
        assert has_final_failure_cheats(code, "lean") is True

    def test_get_cheat_message_single_warning(self):
        """Should generate warning message for single cheat."""
        cheats = [(r"\bsorry\b", "uses 'sorry' to bypass verification")]
        message = get_cheat_message(cheats, is_final=False)
        assert "WARNING" in message
        assert "sorry" in message
        assert "subsequent iterations" in message

    def test_get_cheat_message_multiple_warnings(self):
        """Should generate warning message for multiple cheats."""
        cheats = [
            (r"\bsorry\b", "uses 'sorry' to bypass verification"),
            (r"\badmit\b", "uses 'admit' to bypass verification"),
        ]
        message = get_cheat_message(cheats, is_final=False)
        assert "WARNING" in message
        assert "sorry" in message
        assert "admit" in message

    def test_get_cheat_message_single_final_error(self):
        """Should generate error message for single cheat in final iteration."""
        cheats = [(r"\bsorry\b", "uses 'sorry' to bypass verification")]
        message = get_cheat_message(cheats, is_final=True)
        assert "FINAL VERIFICATION FAILED" in message
        assert "sorry" in message
        assert "not allowed for final" in message

    def test_get_cheat_message_multiple_final_errors(self):
        """Should generate error message for multiple cheats in final iteration."""
        cheats = [
            (r"\bsorry\b", "uses 'sorry' to bypass verification"),
            (r"\badmit\b", "uses 'admit' to bypass verification"),
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


class TestEditableSectionEdgeCases:
    """Test edge cases for editable section handling."""

    def test_nested_editable_tags(self):
        """Should handle nested editable tags correctly."""
        code = """
<vc-definitions>
axiom outer : True
<vc-definitions>
lemma inner : True := sorry  -- Detected (in editable section)
</vc-definitions>
</vc-definitions>

theorem test : True := by
  sorry  -- Ignored (not in editable section)
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 2  # sorry and axiom both inside editable section

    def test_incomplete_editable_tags(self):
        """Should handle incomplete editable tags gracefully."""
        code = """
<vc-definitions>
lemma incomplete : True := sorry
-- Missing closing tag

theorem test : True := by
  sorry
"""
        # The regex should not match incomplete tags, so no sorries should be detected
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0  # No complete editable sections

    def test_empty_editable_section(self):
        """Should handle empty editable sections correctly."""
        code = """
<vc-helpers>
</vc-helpers>

theorem test : True := by
  sorry  -- Ignored (not in editable section)
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 0

    def test_editable_section_with_multiline_content(self):
        """Should handle multiline editable section content correctly."""
        code = """
<vc-definitions>
axiom test_axiom : True

lemma helper_lemma : True := by
  sorry  -- Detected (in editable section)
  
def helper_function : Nat := 42
</vc-definitions>

theorem main : True := by
  sorry  -- Ignored (not in editable section)
"""
        cheats = check_for_cheats(code, "lean")
        assert len(cheats) == 2  # sorry and axiom both inside editable section
