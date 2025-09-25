// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures forall i :: 0 <= i < s.Length ==> min <= s[i]
  ensures exists i :: 0 <= i < s.Length && min == s[i]
// </vc-spec>
// <vc-code>
{
  min := s[0];
  for i := 1 to s.Length
    invariant 0 <= i <= s.Length
    invariant forall k :: 0 <= k < i ==> min <= s[k]
    invariant exists k :: 0 <= k < i && min == s[k]
  {
    if s[i] < min
    {
      min := s[i];
    }
  }
}
// </vc-code>
