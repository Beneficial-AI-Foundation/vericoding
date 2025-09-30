// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ExtractRearChars(s: array<array<char>>) returns (result: array<char>)
    requires forall i :: 0 <= i < s.Length ==> s[i].Length > 0
    ensures s.Length == result.Length
    ensures forall i :: 0 <= i < s.Length ==> result[i] == s[i][s[i].Length - 1]
// </vc-spec>
// <vc-code>
{
  result := new char[s.Length];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant result.Length == s.Length
    invariant forall j :: 0 <= j < i ==> result[j] == s[j][s[j].Length - 1]
  {
    result[i] := s[i][s[i].Length - 1];
    i := i + 1;
  }
}
// </vc-code>
