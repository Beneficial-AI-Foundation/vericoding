// <vc-preamble>
// Helper predicate to determine if a string represents a valid real number
predicate IsValidRealString(s: string)
{
  true  // Simplified implementation
}

// Helper function to convert a valid real string to a real number
function StringToReal(s: string): real
  requires IsValidRealString(s)
{
  0.0  // Simplified implementation
}

// Helper function to split a string by a separator
function SplitString(input: string, sep: string): seq<string>
  requires sep != ""
{
  [input]  // Simplified implementation
}

// Helper function to trim whitespace from a string
function TrimString(s: string): string
{
  s  // Simplified implementation
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method fromstring(input: string, sep: string, n: nat) returns (result: seq<real>)
  // Preconditions: separator is not empty and splitting produces exactly n parts
  requires sep != ""
  requires |SplitString(input, sep)| == n
  requires forall i :: 0 <= i < n ==> 
    var parts := SplitString(input, sep);
    var trimmed := TrimString(parts[i]);
    trimmed != "" && IsValidRealString(trimmed)
  
  // Postconditions: result has correct length and values
  ensures |result| == n
  ensures forall i :: 0 <= i < n ==> result[i] == StringToReal(TrimString(SplitString(input, sep)[i]))
// </vc-spec>
// <vc-code>
{
  var parts := SplitString(input, sep);
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == StringToReal(TrimString(parts[j]))
  {
    var trimmed := TrimString(parts[i]);
    var realVal := StringToReal(trimmed);
    result := result + [realVal];
    i := i + 1;
  }
}
// </vc-code>
