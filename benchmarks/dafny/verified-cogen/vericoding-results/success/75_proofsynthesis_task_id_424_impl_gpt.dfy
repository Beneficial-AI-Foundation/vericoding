// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function lastIndex(n: int): int
  requires n > 0
  ensures 0 <= lastIndex(n) < n
{
  n - 1
}
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
    invariant forall k :: 0 <= k < i ==> result[k] == s[k][s[k].Length - 1]
    decreases s.Length - i
  {
    result[i] := s[i][s[i].Length - 1];
    i := i + 1;
  }
}
// </vc-code>
