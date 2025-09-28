// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method ReverseString(s: array<char>) returns (result: array<char>)
    ensures
        result.Length == s.Length &&
        forall i :: 0 <= i < s.Length ==> result[i] == s[s.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
  result := new char[s.Length];
  for i := 0 to s.Length
  invariant 0 <= i <= s.Length
  invariant forall j :: 0 <= j < i ==> result[j] == s[s.Length - 1 - j]
  {
    if i < s.Length {
      result[i] := s[s.Length - 1 - i];
    }
  }
}
// </vc-code>
