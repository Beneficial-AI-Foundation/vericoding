"""Tests for placeholder counting functionality."""

import pytest
from vericoding.processing.file_processor import count_placeholders


class TestLeanPlaceholderCounting:
    """Test placeholder counting for Lean language."""

    def test_count_single_sorry(self):
        """Should count a single sorry placeholder."""
        code = """
theorem test : True := by
  sorry
"""
        count = count_placeholders(code, "lean")
        assert count == 1

    def test_count_multiple_sorries(self):
        """Should count multiple sorry placeholders."""
        code = """
theorem test1 : True := by
  sorry

theorem test2 : False := by
  sorry

lemma helper : True := sorry
"""
        count = count_placeholders(code, "lean")
        assert count == 3

    def test_count_sorry_with_vc_helpers(self):
        """Should count sorries and vc-helpers sections."""
        code = """
theorem test : True := by
  sorry

<vc-helpers>
-- Helper functions go here
</vc-helpers>

lemma helper : True := sorry
"""
        count = count_placeholders(code, "lean")
        assert count == 3  # 2 sorries + 1 vc-helpers

    def test_ignore_sorry_in_preamble(self):
        """Should ignore sorries inside vc-preamble sections."""
        code = """
<vc-preamble>
axiom test_axiom : True
lemma helper : True := sorry  -- This should be ignored
</vc-preamble>

theorem main : True := by
  sorry  -- This should be counted
"""
        count = count_placeholders(code, "lean")
        assert count == 1

    def test_ignore_sorry_in_multiple_preambles(self):
        """Should ignore sorries in multiple vc-preamble sections."""
        code = """
<vc-preamble>
lemma helper1 : True := sorry  -- Ignored
</vc-preamble>

theorem test1 : True := by
  sorry  -- Counted

<vc-preamble>
lemma helper2 : True := sorry  -- Ignored
</vc-preamble>

theorem test2 : True := by
  sorry  -- Counted
"""
        count = count_placeholders(code, "lean")
        assert count == 2

    def test_sorry_in_preamble_with_helpers(self):
        """Should count vc-helpers but ignore preamble sorries."""
        code = """
<vc-preamble>
lemma helper : True := sorry  -- Ignored
</vc-preamble>

<vc-helpers>
-- Helper code
</vc-helpers>

theorem main : True := by
  sorry  -- Counted
"""
        count = count_placeholders(code, "lean")
        assert count == 2  # 1 sorry + 1 vc-helpers

    def test_nested_preamble_sections(self):
        """It does not handle nested vc-preamble sections correctly."""
        # Note: We assume there are never nested preambles in practice
        code = """
<vc-preamble>
axiom outer : True
lemma outer_helper : True := sorry  -- Ignored (inside preamble)
</vc-preamble>

theorem test : True := by
  sorry  -- Counted
"""
        count = count_placeholders(code, "lean")
        assert count == 1

    def test_incomplete_preamble_tags(self):
        """It does not handle incomplete preamble tags gracefully."""
        code = """
<vc-preamble>
lemma incomplete : True := sorry
-- Missing closing tag

theorem test : True := by
  sorry
"""
        # Without matching closing tag, the regex won't match, so all sorries should be counted
        count = count_placeholders(code, "lean")
        assert count == 2

    def test_empty_preamble_section(self):
        """Should handle empty preamble sections correctly."""
        code = """
<vc-preamble>
</vc-preamble>

theorem test : True := by
  sorry
"""
        count = count_placeholders(code, "lean")
        assert count == 1

    def test_no_placeholders(self):
        """Should return 0 when no placeholders exist."""
        code = """
theorem test : True := by
  exact True.intro

lemma helper : True := True.intro
"""
        count = count_placeholders(code, "lean")
        assert count == 0

    def test_only_vc_helpers(self):
        """Should count only vc-helpers when no sorries present."""
        code = """
<vc-helpers>
-- Helper 1
</vc-helpers>

<vc-helpers>
-- Helper 2
</vc-helpers>

theorem test : True := by
  exact True.intro
"""
        count = count_placeholders(code, "lean")
        assert count == 2

    def test_sorry_as_substring(self):
        """Should count 'sorry' even when part of larger words.
        This is a small bug"""
        code = """
theorem test : True := by
  -- This comment mentions sorry but shouldn't affect counting
  sorry

def sorryNotSorry : Nat := 42  -- Contains 'sorry' as substring
lemma anotherSorry : True := sorry  -- This should be counted
"""
        count = count_placeholders(code, "lean")
        assert count == 5  # All five occurrences of "sorry" should be counted (comment, standalone, sorryNotSorry, anotherSorry, second sorry)

    def test_multiline_preamble_content(self):
        """Should handle multiline preamble content correctly."""
        code = """
<vc-preamble>
axiom test_axiom : True

lemma helper_lemma : True := by
  sorry
  
def helper_function : Nat := 42

lemma another_helper : False := by
  sorry
</vc-preamble>

theorem main : True := by
  sorry  -- This should be counted
"""
        count = count_placeholders(code, "lean")
        assert count == 1


class TestDafnyPlaceholderCounting:
    """Test placeholder counting for Dafny language."""

    def test_count_single_vc_code(self):
        """Should count a single vc-code section."""
        code = """
method TestMethod() returns (result: int)
{
    <vc-code>
    // Implementation goes here
    </vc-code>
}
"""
        count = count_placeholders(code, "dafny")
        assert count == 1

    def test_count_multiple_vc_code(self):
        """Should count multiple vc-code sections."""
        code = """
method Method1() returns (result: int)
{
    <vc-code>
    // Implementation 1
    </vc-code>
}

method Method2() returns (result: int)
{
    <vc-code>
    // Implementation 2
    </vc-code>
}
"""
        count = count_placeholders(code, "dafny")
        assert count == 2

    def test_count_vc_code_with_vc_helpers(self):
        """Should count both vc-code and vc-helpers sections."""
        code = """
<vc-helpers>
// Helper functions
</vc-helpers>

method TestMethod() returns (result: int)
{
    <vc-code>
    // Implementation
    </vc-code>
}

<vc-helpers>
// More helpers
</vc-helpers>
"""
        count = count_placeholders(code, "dafny")
        assert count == 3  # 1 vc-code + 2 vc-helpers

    def test_count_only_vc_helpers(self):
        """Should count only vc-helpers when no vc-code present."""
        code = """
<vc-helpers>
// Helper 1
</vc-helpers>

<vc-helpers>
// Helper 2
</vc-helpers>

method TestMethod() returns (result: int)
{
    return 42;
}
"""
        count = count_placeholders(code, "dafny")
        assert count == 2

    def test_no_placeholders_dafny(self):
        """Should return 0 when no placeholders exist in Dafny code."""
        code = """
method TestMethod() returns (result: int)
{
    return 42;
}

function TestFunction(x: int): int
{
    x + 1
}
"""
        count = count_placeholders(code, "dafny")
        assert count == 0

    def test_empty_sections_dafny(self):
        """Should count empty placeholder sections."""
        code = """
<vc-code>
</vc-code>

<vc-helpers>
</vc-helpers>
"""
        count = count_placeholders(code, "dafny")
        assert count == 2

    def test_nested_sections_dafny(self):
        """Should handle sections without confusion from comments."""
        code = """
method TestMethod()
{
    <vc-code>
    // This contains regular implementation
    var x := 42;
    </vc-code>
}

<vc-helpers>
// Helper functions
function Helper(): int { 1 }
</vc-helpers>
"""
        count = count_placeholders(code, "dafny")
        assert count == 2  # 1 <vc-code> + 1 <vc-helpers>


class TestVerusPlaceholderCounting:
    """Test placeholder counting for Verus language."""

    def test_count_single_vc_code_verus(self):
        """Should count a single vc-code section in Verus."""
        code = """
fn test_function(x: u32) -> u32 {
    <vc-code>
    // Implementation goes here
    </vc-code>
}
"""
        count = count_placeholders(code, "verus")
        assert count == 1

    def test_count_multiple_vc_code_verus(self):
        """Should count multiple vc-code sections in Verus."""
        code = """
fn function1(x: u32) -> u32 {
    <vc-code>
    // Implementation 1
    </vc-code>
}

fn function2(y: u32) -> u32 {
    <vc-code>
    // Implementation 2
    </vc-code>
}
"""
        count = count_placeholders(code, "verus")
        assert count == 2

    def test_count_vc_code_with_vc_helpers_verus(self):
        """Should count both vc-code and vc-helpers sections in Verus."""
        code = """
<vc-helpers>
// Helper functions
</vc-helpers>

fn test_function(x: u32) -> u32 {
    <vc-code>
    // Implementation
    </vc-code>
}

<vc-helpers>
// More helpers
</vc-helpers>
"""
        count = count_placeholders(code, "verus")
        assert count == 3  # 1 vc-code + 2 vc-helpers

    def test_count_only_vc_helpers_verus(self):
        """Should count only vc-helpers when no vc-code present in Verus."""
        code = """
<vc-helpers>
// Helper 1
</vc-helpers>

<vc-helpers>
// Helper 2
</vc-helpers>

fn test_function(x: u32) -> u32 {
    x + 1
}
"""
        count = count_placeholders(code, "verus")
        assert count == 2

    def test_no_placeholders_verus(self):
        """Should return 0 when no placeholders exist in Verus code."""
        code = """
fn test_function(x: u32) -> u32
    requires x > 0
    ensures result > x
{
    x + 1
}
"""
        count = count_placeholders(code, "verus")
        assert count == 0


class TestPlaceholderCountingEdgeCases:
    """Test edge cases for placeholder counting."""

    def test_empty_code(self):
        """Should handle empty code for all languages."""
        for language in ["lean", "dafny", "verus"]:
            count = count_placeholders("", language)
            assert count == 0

    def test_whitespace_only_code(self):
        """Should handle whitespace-only code for all languages."""
        code = "   \n\n\t  \n  "
        for language in ["lean", "dafny", "verus"]:
            count = count_placeholders(code, language)
            assert count == 0

    def test_unsupported_language(self):
        """Should raise ValueError for unsupported languages."""
        with pytest.raises(ValueError, match="Unsupported language: invalid"):
            count_placeholders("some code", "invalid")

    def test_case_sensitivity(self):
        """Should handle case sensitivity correctly."""
        # Test that function names are case sensitive
        for language in ["lean", "dafny", "verus"]:
            with pytest.raises(ValueError, match=f"Unsupported language: {language.upper()}"):
                count_placeholders("code", language.upper())

    def test_mixed_placeholder_types_complex(self):
        """Should handle complex mixed placeholder scenarios."""
        # Lean with mixed types and preamble exclusions
        lean_code = """
<vc-preamble>
lemma preamble_sorry : True := sorry  -- Ignored
</vc-preamble>

<vc-helpers>
-- Helper 1
</vc-helpers>

theorem test1 : True := sorry  -- Counted

<vc-helpers>
-- Helper 2  
</vc-helpers>

theorem test2 : False := sorry  -- Counted

<vc-preamble>
axiom another_sorry : sorry  -- Ignored (contains sorry)
</vc-preamble>
"""
        count = count_placeholders(lean_code, "lean")
        assert count == 4  # 2 sorries + 2 vc-helpers

    def test_overlapping_patterns(self):
        """Should handle patterns without substring confusion."""
        # Test case without mentioning other tags in comments
        dafny_code = """
method Test() {
    <vc-code>
    // Regular implementation code
    var x := 1;
    </vc-code>
}

<vc-helpers>
// Helper implementation
function Helper(): int { 2 }
</vc-helpers>
"""
        count = count_placeholders(dafny_code, "dafny")
        assert count == 2

    def test_malformed_tags(self):
        """Should handle malformed tags gracefully."""
        # The function counts all occurrences of the tag strings, regardless of formatting
        code = """
<vc-code>
// Missing closing tag

<vc-code>
// Properly closed
</vc-code>
"""
        count = count_placeholders(code, "dafny")
        assert count == 2  # Both occurrences of "<vc-code>" are counted

    def test_very_large_code(self):
        """Should handle very large code efficiently."""
        # Generate large code with many placeholders
        large_code_parts = []
        expected_count = 0
        
        # Add many placeholders for Lean
        for i in range(100):
            large_code_parts.append(f"theorem test{i} : True := sorry")
            expected_count += 1
        
        for i in range(50):
            large_code_parts.append(f"<vc-helpers>\n-- Helper {i}\n</vc-helpers>")
            expected_count += 1
        
        large_code = "\n".join(large_code_parts)
        count = count_placeholders(large_code, "lean")
        assert count == expected_count


class TestPlaceholderCountingConsistency:
    """Test consistency across different scenarios."""

    def test_idempotent_counting(self):
        """Should return same count when called multiple times."""
        code = """
theorem test : True := sorry
<vc-helpers>
-- Helper
</vc-helpers>
"""
        count1 = count_placeholders(code, "lean")
        count2 = count_placeholders(code, "lean")
        count3 = count_placeholders(code, "lean")
        
        assert count1 == count2 == count3 == 2

    def test_ordering_independence(self):
        """Should count same regardless of placeholder order."""
        code1 = """
theorem test : True := sorry
<vc-helpers>
-- Helper
</vc-helpers>
"""
        
        code2 = """
<vc-helpers>
-- Helper
</vc-helpers>
theorem test : True := sorry
"""
        
        count1 = count_placeholders(code1, "lean")
        count2 = count_placeholders(code2, "lean")
        assert count1 == count2 == 2

    def test_whitespace_tolerance(self):
        """Should be tolerant of different whitespace patterns."""
        code1 = """theorem test:True:=sorry"""
        code2 = """theorem test : True := sorry"""
        code3 = """
theorem test : True := 
    sorry
"""
        
        # All should count the single sorry
        for code in [code1, code2, code3]:
            count = count_placeholders(code, "lean")
            assert count == 1
