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
function FieldValue(fieldStr: string, fillValue: real): real {
  if IsEmpty(fieldStr) || IsWhitespaceOnly(Trim(fieldStr)) then fillValue
  else if IsValidNatString(Trim(fieldStr)) then ParseNatToReal(Trim(fieldStr))
  else fillValue
}
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
  var out: seq<seq<real>> := [];
  var i := skipHeader;
  while i < |input|
    invariant skipHeader <= i <= |input|
    invariant |out| == i - skipHeader
    invariant forall ii :: 0 <= ii < |out| ==> |out[ii]| == cols
    invariant forall ii, jj :: 0 <= ii < |out| && 0 <= jj < cols ==>
      out[ii][jj] == (if IsEmpty(Split(input[ii + skipHeader], delimiter)[jj]) || IsWhitespaceOnly(Trim(Split(input[ii + skipHeader], delimiter)[jj])) then fillValue else if IsValidNatString(Trim(Split(input[ii + skipHeader], delimiter)[jj])) then ParseNatToReal(Trim(Split(input[ii + skipHeader], delimiter)[jj])) else fillValue)
  {
    var fields := Split(input[i], delimiter);
    var j := 0;
    var row: seq<real> := [];
    while j < cols
      invariant 0 <= j <= cols
      invariant |row| == j
      invariant forall jj :: 0 <= jj < j ==> row[jj] == (if IsEmpty(fields[jj]) || IsWhitespaceOnly(Trim(fields[jj])) then fillValue else if IsValidNatString(Trim(fields[jj])) then ParseNatToReal(Trim(fields[jj])) else fillValue)
    {
      var fieldStr := fields[j];
      var trimmed := Trim(fieldStr);
      var value: real;
      if IsEmpty(fieldStr) || IsWhitespaceOnly(trimmed) {
        value := fillValue;
      } else if IsValidNatString(trimmed) {
        value := ParseNatToReal(trimmed);
      } else {
        value := fillValue;
      }
      row := row + [value];
      j := j + 1;
    }
    out := out + [row];
    i := i + 1;
  }
  result := out;
}

// </vc-code>
