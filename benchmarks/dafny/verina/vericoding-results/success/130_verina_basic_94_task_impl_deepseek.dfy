// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method IterCopy(s: array<int>) returns (result: array<int>)
    ensures
        s.Length == result.Length &&
        forall i :: 0 <= i < s.Length ==> s[i] == result[i]
// </vc-spec>
// <vc-code>
{
  result := new int[s.Length];
  var index := 0;
  while index < s.Length
    invariant 0 <= index <= s.Length
    invariant forall i :: 0 <= i < index ==> s[i] == result[i]
  {
    result[index] := s[index];
    index := index + 1;
  }
}
// </vc-code>
