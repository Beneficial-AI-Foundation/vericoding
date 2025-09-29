// <vc-preamble>
// Helper predicate to check if a character is alphanumeric
predicate isAlphaNumeric(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z') || ('0' <= c <= '9')
}

// Helper predicate to check if a character is an allowed formatting character
predicate isAllowedChar(c: char)
{
    isAlphaNumeric(c) || c == '[' || c == ']' || c == '(' || c == ')' || 
    c == ',' || c == ' ' || c == '.' || c == '-' || c == '+'
}

// Helper predicate to check if all characters in a string are allowed
predicate allCharsAllowed(s: string)
{
    forall i :: 0 <= i < |s| ==> isAllowedChar(s[i])
}

// Helper predicate to check if a string starts with a given prefix
predicate startsWith(s: string, prefix: string)
{
    |s| >= |prefix| && s[0..|prefix|] == prefix
}

// Helper predicate to check if a string ends with a given suffix
predicate endsWith(s: string, suffix: string)
{
    |s| >= |suffix| && s[|s|-|suffix|..] == suffix
}

// Helper predicate to check if a string contains a specific character
predicate contains(s: string, c: char)
{
    exists i :: 0 <= i < |s| && s[i] == c
}

/**
 * Returns the string representation of an array formatted as "array([v1, v2, ..., vn])".
 * Provides a structured string representation with configurable precision and formatting options.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method array_repr(arr: seq<real>, max_line_width: nat, precision: nat, suppress_small: bool) returns (result: string)
    requires precision > 0
    requires max_line_width > 0
    ensures |result| > 0  // Non-empty result
    ensures startsWith(result, "array([")  // Basic format structure start
    ensures endsWith(result, "])")  // Basic format structure end
    ensures |arr| == 0 ==> result == "array([])"  // Empty array case
    ensures |arr| > 1 ==> contains(result, ',')  // Non-empty array case with multiple elements
    ensures |arr| == 1 ==> !contains(result, ',')  // Single element case
    ensures allCharsAllowed(result)  // Structural consistency
    ensures |result| <= max_line_width + 20  // Precision constraint
    ensures contains(result, '(') && contains(result, ')')  // Format correctness - parentheses
    ensures contains(result, '[') && contains(result, ']')  // Format correctness - brackets
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
