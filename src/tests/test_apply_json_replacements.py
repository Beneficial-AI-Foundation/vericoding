"""
Comprehensive tests for apply_json_replacements function.

Tests cover all three supported languages (Lean, Dafny, Verus) with various scenarios:
- Basic replacements
- Mixed placeholder types
- Error handling
- Edge cases
- Order preservation
"""

import pytest
from unittest.mock import Mock
from vericoding.processing.code_fixer import apply_json_replacements
from vericoding.core.config import ProcessingConfig


class MockLanguageConfig:
    """Mock language config for testing."""

    def __init__(self, file_extension: str = ".rs"):
        self.file_extension = file_extension


@pytest.fixture
def lean_config():
    """Create a mock Lean config."""
    config = Mock(spec=ProcessingConfig)
    config.language = "lean"
    config.language_config = MockLanguageConfig(".lean")
    return config


@pytest.fixture
def dafny_config():
    """Create a mock Dafny config."""
    config = Mock(spec=ProcessingConfig)
    config.language = "dafny"
    config.language_config = MockLanguageConfig(".dfy")
    return config


@pytest.fixture
def verus_config():
    """Create a mock Verus config."""
    config = Mock(spec=ProcessingConfig)
    config.language = "verus"
    config.language_config = MockLanguageConfig(".rs")
    return config


class TestLeanReplacements:
    """Test JSON replacements for Lean language."""

    def test_single_sorry_replacement(self, lean_config):
        """Test replacing a single sorry."""
        original_code = """
<vc-definitions>
def factorial (n : Nat) : Nat := sorry
</vc-definitions>
"""
        llm_response = """["n.factorial"]"""

        expected_result = """
<vc-definitions>
def factorial (n : Nat) : Nat := n.factorial
</vc-definitions>
"""

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_multiple_sorry_replacements(self, lean_config):
        """Test replacing multiple sorry placeholders."""
        original_code = """
<vc-definitions>
def factorial (n : Nat) : Nat := sorry

def fibonacci (n : Nat) : Nat := sorry
</vc-definitions>

<vc-theorems>
theorem factorial_pos (n : Nat) : factorial n > 0 := sorry
</vc-theorems>
"""
        llm_response = """["n.factorial", "if n < 2 then 1 else fibonacci (n-1) + fibonacci (n-2)", "by simp [factorial]"]"""

        expected_result = """
<vc-definitions>
def factorial (n : Nat) : Nat := n.factorial

def fibonacci (n : Nat) : Nat := if n < 2 then 1 else fibonacci (n-1) + fibonacci (n-2)
</vc-definitions>

<vc-theorems>
theorem factorial_pos (n : Nat) : factorial n > 0 := by simp [factorial]
</vc-theorems>
"""

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_single_vc_helpers_replacement(self, lean_config):
        """Test replacing a single vc-helpers section."""
        original_code = """
<vc-helpers>
-- Helper functions go here
</vc-helpers>

def main_function : Nat := 42
"""
        llm_response = """["-- LLM HELPER\\nlemma helper_lemma : True := by trivial"]"""

        expected_result = """
<vc-helpers>
-- LLM HELPER
lemma helper_lemma : True := by trivial
</vc-helpers>

def main_function : Nat := 42
"""

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_mixed_sorry_and_vc_helpers(self, lean_config):
        """Test replacing both sorry and vc-helpers in correct order."""
        original_code = """
<vc-helpers>
-- Helper code here
</vc-helpers>

<vc-definitions>
def factorial (n : Nat) : Nat := sorry
</vc-definitions>

<vc-theorems>
theorem factorial_pos (n : Nat) : factorial n > 0 := sorry
</vc-theorems>
"""
        llm_response = """["-- LLM HELPER\\nlemma nat_pos : ∀ n, n.factorial > 0 := by trivial", "n.factorial", "by apply nat_pos"]"""

        expected_result = """
<vc-helpers>
-- LLM HELPER
lemma nat_pos : ∀ n, n.factorial > 0 := by trivial
</vc-helpers>

<vc-definitions>
def factorial (n : Nat) : Nat := n.factorial
</vc-definitions>

<vc-theorems>
theorem factorial_pos (n : Nat) : factorial n > 0 := by apply nat_pos
</vc-theorems>
"""

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_wrong_replacement_count_lean(self, lean_config):
        """Test error when replacement count doesn't match placeholder count."""
        original_code = """
<vc-definitions>
def factorial (n : Nat) : Nat := sorry
def fibonacci (n : Nat) : Nat := sorry
</vc-definitions>
"""
        llm_response = """["n.factorial"]"""  # Only 1 replacement for 2 sorries

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is not None
        assert "JSON replacement count mismatch" in error
        assert "Expected 2 replacements" in error
        assert "got 1" in error

    def test_no_placeholders_lean(self, lean_config):
        """Test when there are no placeholders to replace."""
        original_code = """
def factorial (n : Nat) : Nat := n.factorial
"""
        llm_response = """[]"""

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert result == original_code


class TestDafnyReplacements:
    """Test JSON replacements for Dafny language."""

    def test_single_vc_code_replacement(self, dafny_config):
        """Test replacing a single vc-code section."""
        original_code = """
method FindMax(a: array<int>) returns (max: int)
{
    <vc-code>
    // Implementation here
    </vc-code>
}
"""
        llm_response = """["max := a[0];\\n    for i := 1 to a.Length {\\n        if a[i] > max { max := a[i]; }\\n    }"]"""

        expected_result = """
method FindMax(a: array<int>) returns (max: int)
{
    <vc-code>
max := a[0];
    for i := 1 to a.Length {
        if a[i] > max { max := a[i]; }
    }
    </vc-code>
}
"""

        result, error = apply_json_replacements(
            dafny_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_multiple_vc_code_replacements(self, dafny_config):
        """Test replacing multiple vc-code sections."""
        original_code = """
method Method1()
{
    <vc-code>
    // First implementation
    </vc-code>
}

method Method2() 
{
    <vc-code>
    // Second implementation  
    </vc-code>
}
"""
        llm_response = (
            """["var x := 0;\\n    x := x + 1;", "var y := 42;\\n    return y;"]"""
        )

        expected_result = """
method Method1()
{
    <vc-code>
var x := 0;
    x := x + 1;
    </vc-code>
}

method Method2() 
{
    <vc-code>
var y := 42;
    return y;
    </vc-code>
}
"""

        result, error = apply_json_replacements(
            dafny_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_single_vc_helpers_replacement(self, dafny_config):
        """Test replacing a single vc-helpers section."""
        original_code = """
<vc-helpers>
// Helper functions
</vc-helpers>

method MainMethod() 
{
    var x := 0;
}
"""
        llm_response = """["function Helper(x: int): int { x + 1 }\\n\\nlemma HelperProperty(x: int)\\n    ensures Helper(x) == x + 1\\n{\\n}"]"""

        result, error = apply_json_replacements(
            dafny_config, original_code, llm_response
        )

        assert error is None
        assert "function Helper" in result
        assert "lemma HelperProperty" in result
        assert "Helper functions" not in result

    def test_mixed_vc_code_and_vc_helpers(self, dafny_config):
        """Test replacing both vc-code and vc-helpers in correct order."""
        original_code = """
<vc-helpers>
// Helper code
</vc-helpers>

method FindMax(a: array<int>) returns (max: int)
{
    <vc-code>
    // Implementation
    </vc-code>
}

<vc-helpers>
// More helpers
</vc-helpers>
"""
        llm_response = """["function IsPositive(x: int): bool { x > 0 }", "max := 0;\\n    for i := 0 to a.Length {\\n        if a[i] > max { max := a[i]; }\\n    }", "lemma MaxIsMax()\\n    ensures true\\n{\\n}"]"""

        expected_result = """
<vc-helpers>
function IsPositive(x: int): bool { x > 0 }
</vc-helpers>

method FindMax(a: array<int>) returns (max: int)
{
    <vc-code>
max := 0;
    for i := 0 to a.Length {
        if a[i] > max { max := a[i]; }
    }
    </vc-code>
}

<vc-helpers>
lemma MaxIsMax()
    ensures true
{
}
</vc-helpers>
"""

        result, error = apply_json_replacements(
            dafny_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_wrong_replacement_count_dafny(self, dafny_config):
        """Test error when replacement count doesn't match."""
        original_code = """
<vc-code>
// First
</vc-code>

<vc-code>
// Second  
</vc-code>
"""
        llm_response = """["var x := 0;"]"""  # Only 1 replacement for 2 sections

        result, error = apply_json_replacements(
            dafny_config, original_code, llm_response
        )

        assert error is not None
        assert "JSON replacement count mismatch" in error
        assert "Expected 2 replacements" in error
        assert "got 1" in error


class TestVerusReplacements:
    """Test JSON replacements for Verus language."""

    def test_single_vc_code_replacement(self, verus_config):
        """Test replacing a single vc-code section."""
        original_code = """
fn binary_search(arr: &Vec<i32>, target: i32) -> Option<usize> {
    <vc-code>
    // Binary search implementation
    </vc-code>
}
"""
        llm_response = """["let mut low = 0;\\n    let mut high = arr.len();\\n    while low < high {\\n        let mid = low + (high - low) / 2;\\n        if arr[mid] == target {\\n            return Some(mid);\\n        }\\n        if arr[mid] < target {\\n            low = mid + 1;\\n        } else {\\n            high = mid;\\n        }\\n    }\\n    None"]"""

        expected_result = """
fn binary_search(arr: &Vec<i32>, target: i32) -> Option<usize> {
    <vc-code>
let mut low = 0;
    let mut high = arr.len();
    while low < high {
        let mid = low + (high - low) / 2;
        if arr[mid] == target {
            return Some(mid);
        }
        if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    None
    </vc-code>
}
"""

        result, error = apply_json_replacements(
            verus_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_multiple_vc_code_replacements(self, verus_config):
        """Test replacing multiple vc-code sections."""
        original_code = """
fn function1() -> i32 {
    <vc-code>
    // Implementation 1
    </vc-code>
}

fn function2() -> i32 {
    <vc-code>
    // Implementation 2
    </vc-code>
}
"""
        llm_response = """["let x = 42;\\n    x", "let y = 84;\\n    y * 2"]"""

        result, error = apply_json_replacements(
            verus_config, original_code, llm_response
        )

        assert error is None
        assert "let x = 42" in result
        assert "let y = 84" in result
        assert "Implementation 1" not in result
        assert "Implementation 2" not in result

    def test_single_vc_helpers_replacement(self, verus_config):
        """Test replacing a single vc-helpers section."""
        original_code = """
<vc-helpers>
// Helper functions and proofs
</vc-helpers>

fn main_function() -> i32 {
    42
}
"""
        llm_response = """["proof fn helper_proof() {\\n    // proof body\\n}\\n\\nfn utility_function(x: i32) -> i32 {\\n    x + 1\\n}"]"""

        result, error = apply_json_replacements(
            verus_config, original_code, llm_response
        )

        assert error is None
        assert "proof fn helper_proof" in result
        assert "fn utility_function" in result
        assert "Helper functions and proofs" not in result

    def test_mixed_vc_code_and_vc_helpers(self, verus_config):
        """Test replacing both vc-code and vc-helpers in correct order."""
        original_code = """
<vc-helpers>
// Helpers first
</vc-helpers>

fn main_function(x: i32) -> i32 
    requires x >= 0
    ensures result >= x
{
    <vc-code>
    // Main implementation
    </vc-code>
}

<vc-helpers>
// More helpers
</vc-helpers>
"""
        llm_response = """["proof fn lemma1() {\\n    // proof\\n}", "let y = helper_function(x);\\n    y + 1", "fn helper_function(n: i32) -> i32 {\\n    n * 2\\n}"]"""

        result, error = apply_json_replacements(
            verus_config, original_code, llm_response
        )

        assert error is None
        assert "proof fn lemma1" in result  # First vc-helpers
        assert "let y = helper_function" in result  # vc-code
        assert "fn helper_function(n: i32)" in result  # Second vc-helpers
        assert "Helpers first" not in result
        assert "Main implementation" not in result
        assert "More helpers" not in result


class TestErrorHandling:
    """Test error handling scenarios for all languages."""

    def test_invalid_json_syntax(self, lean_config):
        """Test handling of invalid JSON syntax."""
        original_code = "def test : Nat := sorry"
        llm_response = '''["invalid json syntax"'''  # Missing closing bracket

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is not None
        assert "JSON parsing failed" in error
        # The specific error message depends on whether JSON is found or not
        assert result == original_code  # Original code unchanged

    def test_non_array_json(self, dafny_config):
        """Test handling of non-array JSON."""
        original_code = "<vc-code>\n// Test\n</vc-code>"
        llm_response = """{"not": "an array"}"""

        result, error = apply_json_replacements(
            dafny_config, original_code, llm_response
        )

        assert error is not None
        assert "JSON parsing failed" in error
        assert result == original_code

    def test_non_string_replacement(self, verus_config):
        """Test handling of non-string replacements."""
        original_code = "<vc-code>\n// Test\n</vc-code>"
        llm_response = """[42]"""  # Number instead of string

        result, error = apply_json_replacements(
            verus_config, original_code, llm_response
        )

        assert error is not None
        assert "must be a string" in error
        assert "got <class 'int'>" in error
        assert result == original_code

    def test_no_json_found(self, lean_config):
        """Test handling when no JSON is found in response."""
        original_code = "def test : Nat := sorry"
        llm_response = "This is just regular text with no JSON array"

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is not None
        assert "No JSON array found" in error
        assert result == original_code

    def test_json_in_code_block(self, lean_config):
        """Test extracting JSON from markdown code block."""
        original_code = "<vc-definitions>\\ndef test : Nat := sorry\\n</vc-definitions>"
        llm_response = """
Here's the solution:

```json
["42"]
```

That should work!
"""

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert "42" in result
        assert "sorry" not in result

    def test_malformed_vc_helpers_section(self, dafny_config):
        """Test handling of malformed vc-helpers sections."""
        original_code = """
<vc-helpers>
// Missing closing tag
"""
        llm_response = """["helper code"]"""

        result, error = apply_json_replacements(
            dafny_config, original_code, llm_response
        )

        assert error is not None
        assert (
            "replacement count mismatch" in error
        )  # No valid sections found, so 0 expected but 1 provided


class TestEdgeCases:
    """Test edge cases and boundary conditions."""

    def test_empty_original_code(self, lean_config):
        """Test with empty original code."""
        original_code = ""
        llm_response = """[]"""

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert result == ""

    def test_empty_replacements_array(self, verus_config):
        """Test with empty replacements array when no placeholders exist."""
        original_code = "fn main() { println!('Hello'); }"
        llm_response = """[]"""

        result, error = apply_json_replacements(
            verus_config, original_code, llm_response
        )

        assert error is None
        assert result == original_code

    def test_nested_vc_sections(self, dafny_config):
        """Test handling of nested vc sections (should not be supported)."""
        original_code = """
<vc-code>
    <vc-code>
    // Nested
    </vc-code>
</vc-code>
"""
        llm_response = """["outer", "inner"]"""

        result, error = apply_json_replacements(
            dafny_config, original_code, llm_response
        )

        # Should treat as two separate sections based on opening tags
        assert error is None or "replacement count mismatch" in error

    def test_multiline_replacements(self, lean_config):
        """Test multiline replacement content."""
        original_code = """
<vc-helpers>
// Helper
</vc-helpers>

<vc-definitions>
def test : Nat := sorry
</vc-definitions>
"""
        llm_response = """["-- LLM HELPER\\nlemma helper1 : True := by trivial\\nlemma helper2 : False ∨ True := by simp", "by\\n  have h : True := helper1\\n  have h2 : False ∨ True := helper2\\n  exact 42"]"""

        expected_result = """
<vc-helpers>
-- LLM HELPER
lemma helper1 : True := by trivial
lemma helper2 : False ∨ True := by simp
</vc-helpers>

<vc-definitions>
def test : Nat := by
  have h : True := helper1
  have h2 : False ∨ True := helper2
  exact 42
</vc-definitions>
"""

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_editable_section_sorry_inclusion(self, lean_config):
        """Test that sorries outside editable sections are excluded from replacement."""
        original_code = """
def first : Nat := sorry  -- Not in editable section, should be ignored

axiom protected_axiom : ∀ x : Nat, x = sorry  -- Not in editable section, should be ignored

<vc-definitions>
def second : Nat := sorry  -- In editable section, should be replaced
</vc-definitions>

<vc-helpers>
-- Helper code goes here
</vc-helpers>
"""
        # Only 2 responses - one for the sorry in vc-definitions, one for vc-helpers
        # The sorries outside editable sections should be ignored
        llm_response = """["84", "-- LLM HELPER\\nlemma helper : True := by trivial"]"""

        expected_result = """
def first : Nat := sorry  -- Not in editable section, should be ignored

axiom protected_axiom : ∀ x : Nat, x = sorry  -- Not in editable section, should be ignored

<vc-definitions>
def second : Nat := 84  -- In editable section, should be replaced
</vc-definitions>

<vc-helpers>
-- LLM HELPER
lemma helper : True := by trivial
</vc-helpers>
"""

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_multiple_editable_sections(self, lean_config):
        """Test handling of multiple editable sections."""
        original_code = """
def first : Nat := sorry  -- Ignored (not in editable section)

<vc-definitions>
def second : Nat := sorry  -- Should be replaced
</vc-definitions>

def third : Nat := sorry  -- Ignored (not in editable section)

<vc-theorems>  
theorem fourth : True := sorry  -- Should be replaced
</vc-theorems>

def fifth : Nat := sorry  -- Ignored (not in editable section)
"""
        # Only 2 responses for the 2 sorries inside editable sections
        llm_response = """["42", "by trivial"]"""

        expected_result = """
def first : Nat := sorry  -- Ignored (not in editable section)

<vc-definitions>
def second : Nat := 42  -- Should be replaced
</vc-definitions>

def third : Nat := sorry  -- Ignored (not in editable section)

<vc-theorems>  
theorem fourth : True := by trivial  -- Should be replaced
</vc-theorems>

def fifth : Nat := sorry  -- Ignored (not in editable section)
"""

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_unicode_content(self, lean_config):
        """Test handling of unicode content in replacements."""
        original_code = "<vc-definitions>\\ndef test : Nat := sorry\\n</vc-definitions>"
        llm_response = """["∀ x : ℕ, x + 0 = x"]"""

        expected_result = "<vc-definitions>\\ndef test : Nat := ∀ x : ℕ, x + 0 = x\\n</vc-definitions>"

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_special_characters_in_replacements(self, dafny_config):
        """Test handling of special characters in replacements."""
        original_code = "<vc-code>\n// Test\n</vc-code>"
        llm_response = """["var s := \\"Hello\\\\nWorld\\";\\n    print(s);"]"""

        result, error = apply_json_replacements(
            dafny_config, original_code, llm_response
        )

        assert error is None
        assert 'var s := "Hello' in result
        assert "print(s)" in result


class TestOrderPreservation:
    """Test that replacement order is preserved correctly."""

    def test_lean_mixed_order_preservation(self, lean_config):
        """Test that Lean preserves order of mixed sorry and vc-helpers."""
        original_code = """
<vc-helpers>
-- First helper
</vc-helpers>

<vc-definitions>
def first : Nat := sorry
</vc-definitions>

<vc-helpers>
-- Second helper
</vc-helpers>

<vc-theorems>
theorem second : True := sorry
</vc-theorems>
"""
        llm_response = """["-- Helper 1", "1", "-- Helper 2", "by trivial"]"""

        expected_result = """
<vc-helpers>
-- Helper 1
</vc-helpers>

<vc-definitions>
def first : Nat := 1
</vc-definitions>

<vc-helpers>
-- Helper 2
</vc-helpers>

<vc-theorems>
theorem second : True := by trivial
</vc-theorems>
"""

        result, error = apply_json_replacements(
            lean_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result

    def test_dafny_mixed_order_preservation(self, dafny_config):
        """Test that Dafny preserves order of mixed vc-code and vc-helpers."""
        original_code = """
<vc-helpers>
</vc-helpers>

method Method1() {
    <vc-code>
    // Code 1
    </vc-code>
}

<vc-helpers>
// Helper B
</vc-helpers>

method Method2() {
    <vc-code>
    // Code 2
    </vc-code>
}
"""
        llm_response = """["function HelperA(): int { 1 }", "var x := 1;", "function HelperB(): int { 2 }", "var y := 2;"]"""

        expected_result = """
<vc-helpers>
function HelperA(): int { 1 }
</vc-helpers>

method Method1() {
    <vc-code>
var x := 1;
    </vc-code>
}

<vc-helpers>
function HelperB(): int { 2 }
</vc-helpers>

method Method2() {
    <vc-code>
var y := 2;
    </vc-code>
}
"""

        result, error = apply_json_replacements(
            dafny_config, original_code, llm_response
        )

        assert error is None
        assert result == expected_result


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
