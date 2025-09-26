// <vc-preamble>
// Helper predicates and functions for string operations
predicate IsEmpty(s: string) {
    |s| == 0
}

predicate IsWhitespaceOnly(s: string) {
    forall i :: 0 <= i < |s| ==> s[i] == ' ' || s[i] == '\t' || s[i] == '\n' || s[i] == '\r'
}

function Split(s: string, delimiter: string): seq<string>
    ensures |Split(s, delimiter)| >= 1
{
    // Abstract specification of string splitting - actual implementation would split on delimiter
    [s] // placeholder - in reality this would split properly on delimiter
}

function Trim(s: string): string {
    // Abstract specification of string trimming
    s // placeholder - in reality this would remove leading/trailing whitespace
}

predicate IsValidNatString(s: string) {
    // Check if string represents a valid natural number
    !IsEmpty(s) && !IsWhitespaceOnly(s) && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function ParseNatToReal(s: string): real
    requires IsValidNatString(s)
{
    // Abstract specification of parsing string as nat then converting to real
    0.0 // placeholder - in reality this would parse as nat then convert to real
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method GenFromTxt(input: seq<string>, delimiter: string, fillValue: real, skipHeader: nat, cols: nat) 
    returns (result: seq<seq<real>>)
    requires skipHeader < |input|
    // All data lines (after skipping headers) must have exactly cols fields when split
    requires forall i :: skipHeader <= i < |input| ==> |Split(input[i], delimiter)| == cols
    ensures |result| == |input| - skipHeader
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == cols
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < cols ==>
        var lineIdx := i + skipHeader;
        var line := input[lineIdx];
        var fields := Split(line, delimiter);
        var fieldStr := fields[j];
        var trimmedField := Trim(fieldStr);
        result[i][j] == (if IsEmpty(fieldStr) || IsWhitespaceOnly(trimmedField) then 
                            fillValue 
                         else if IsValidNatString(trimmedField) then
                            ParseNatToReal(trimmedField)
                         else 
                            fillValue)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
