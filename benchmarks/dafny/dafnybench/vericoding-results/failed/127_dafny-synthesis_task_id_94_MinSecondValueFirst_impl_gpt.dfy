

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
// </vc-spec>
// <vc-code>
{
  var min := 0;
  var i := 1;
  while i < s.Length
    invariant 0 <= min < i <= s.Length
    invariant forall j :: 0 <= j < i ==> s[min][1] <= s[j][1]
    decreases s.Length - i
  {
    if s[i][1] < s[min][1] {
      min := i;
    }
    i := i + 1;
  }
  firstOfMinSecond := s[min][0];
}
// </vc-code>

