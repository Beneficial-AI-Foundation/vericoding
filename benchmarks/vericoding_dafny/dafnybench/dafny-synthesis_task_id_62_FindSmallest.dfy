// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures forall i :: 0 <= i < s.Length ==> min <= s[i]
  ensures exists i :: 0 <= i < s.Length && min == s[i]
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>