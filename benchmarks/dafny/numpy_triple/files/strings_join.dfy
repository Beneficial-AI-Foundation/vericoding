// <vc-preamble>
/*
 * Dafny specification for numpy.strings.join
 * 
 * This file specifies the behavior of joining characters within strings using separators.
 * For each pair of separator and sequence, the function joins the individual characters 
 * of the sequence string using the corresponding separator string.
 */

// Helper function to convert a string to a sequence of single-character strings
function StringToCharStrings(s: string): seq<string>
{
    seq(|s|, i requires 0 <= i < |s| => [s[i]])
}

// Helper function to join a sequence of strings with a separator
function JoinStrings(separator: string, strings: seq<string>): string
{
    if |strings| == 0 then ""
    else if |strings| == 1 then strings[0]
    else strings[0] + separator + JoinStrings(separator, strings[1..])
}

// Main method specification for numpy.strings.join
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Join(sep: seq<string>, seq_strings: seq<string>) returns (result: seq<string>)
    requires |sep| == |seq_strings|
    ensures |result| == |sep|
    ensures forall i :: 0 <= i < |result| ==>
        var s := seq_strings[i];
        var separator := sep[i];
        var expected := if |s| <= 1 then s 
                       else JoinStrings(separator, StringToCharStrings(s));
        (
            // Core correctness property
            result[i] == expected &&
            
            // Length property for non-trivial cases  
            (|s| > 1 ==> |result[i]| == |s| + (|s| - 1) * |separator|) &&
            
            // Empty string preservation
            (|s| == 0 ==> result[i] == "") &&
            
            // Single character preservation
            (|s| == 1 ==> result[i] == s) &&
            
            // Non-empty result for non-empty input
            (|s| > 0 ==> |result[i]| > 0) &&
            
            // Character order preservation - all characters in result come from original string or separator
            (|s| > 1 ==> 
                forall j :: 0 <= j < |result[i]| ==> 
                    (exists k :: 0 <= k < |s| && result[i][j] == s[k]) ||
                    (exists k :: 0 <= k < |separator| && result[i][j] == separator[k]))
        )
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
