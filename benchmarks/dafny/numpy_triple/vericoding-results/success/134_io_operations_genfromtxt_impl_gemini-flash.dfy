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
// No helpers needed for this verification task

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
  var tempResult: seq<seq<real>> := [];
  var i := skipHeader;
  while i < |input|
    invariant skipHeader <= i <= |input|
    invariant |tempResult| == i - skipHeader
    invariant forall k :: 0 <= k < |tempResult| ==> |tempResult[k]| == cols
    invariant forall k, l :: 0 <= k < |tempResult| && 0 <= l < cols ==> 
        var lineIdx_inv := k + skipHeader;
        var line_inv := input[lineIdx_inv];
        var fields_inv := Split(line_inv, delimiter);
        var fieldStr_inv := fields_inv[l];
        var trimmedField_inv := Trim(fieldStr_inv);
        tempResult[k][l] == (if IsEmpty(fieldStr_inv) || IsWhitespaceOnly(trimmedField_inv) then 
                                fillValue 
                             else if IsValidNatString(trimmedField_inv) then
                                ParseNatToReal(trimmedField_inv)
                             else 
                                fillValue)
  {
    var currentLine := input[i];
    var fields := Split(currentLine, delimiter);
    var row: seq<real> := [];
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant |row| == j
      invariant forall k :: 0 <= k < |row| ==> 
          var fieldStr_inner := fields[k];
          var trimmedField_inner := Trim(fieldStr_inner);
          row[k] == (if IsEmpty(fieldStr_inner) || IsWhitespaceOnly(trimmedField_inner) then 
                        fillValue 
                     else if IsValidNatString(trimmedField_inner) then
                        ParseNatToReal(trimmedField_inner)
                     else 
                        fillValue)
    {
      var fieldStr := fields[j];
      var trimmedField := Trim(fieldStr);
      var val: real;
      if IsEmpty(fieldStr) || IsWhitespaceOnly(trimmedField) {
        val := fillValue;
      } else if IsValidNatString(trimmedField) {
        val := ParseNatToReal(trimmedField);
      } else {
        val := fillValue;
      }
      row := row + [val];
      j := j + 1;
    }
    tempResult := tempResult + [row];
    i := i + 1;
  }
  result := tempResult;
}
// </vc-code>
