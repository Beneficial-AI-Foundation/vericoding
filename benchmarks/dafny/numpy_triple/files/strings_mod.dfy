// <vc-preamble>
// Helper function to check if a string contains a character
predicate ContainsChar(s: string, c: char)
{
    exists i :: 0 <= i < |s| && s[i] == c
}

// Helper function to represent string formatting behavior
// This is a ghost function that models the expected formatting result
ghost function StringFormat(format_str: string, value_str: string): string
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method StringsMod(a: seq<string>, values: seq<string>) returns (result: seq<string>)
    requires |a| == |values|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==>
        var format_str := a[i];
        var value_str := values[i];
        var formatted := result[i];
        // Correctness: result matches the ghost function specification
        formatted == StringFormat(format_str, value_str) &&
        // Core mathematical properties of string formatting
        (|formatted| >= 0) &&
        // Identity property: format strings without % remain unchanged
        (!ContainsChar(format_str, '%') ==> formatted == format_str) &&
        // Substitution property: format strings with % get interpolated
        (ContainsChar(format_str, '%') ==> formatted != format_str || format_str == "") &&
        // Empty format string property
        (format_str == "" ==> formatted == "") &&
        // Non-empty format strings with % produce non-empty results
        (ContainsChar(format_str, '%') && format_str != "" ==> |formatted| > 0) &&
        // Monotonicity: non-empty format strings preserve non-emptiness appropriately
        (|format_str| > 0 ==> |formatted| >= 0) &&
        // Preservation: result maintains format structure with substitutions
        (ContainsChar(format_str, '%') ==> 
            (|formatted| >= |format_str| - 2 || |formatted| == 0))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
