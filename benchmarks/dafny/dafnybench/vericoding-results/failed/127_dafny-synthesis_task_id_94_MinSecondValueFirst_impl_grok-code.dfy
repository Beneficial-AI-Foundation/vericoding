

// <vc-helpers>
method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: (0 <= i < s.Length && firstOfMinSecond == s[i][0] && (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1]))
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
  var i := 0;
  var minSecond := s[0][1];
  firstOfMinSecond := s[0][0];
  i := 1;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant exists k :: 0 <= k < i && minSecond == s[k][1] && (forall j :: 0 <= j < i ==> minSecond <= s[j][1]) && firstOfMinSecond == s[k][0]
  {
    if s[i][1] < minSecond {
      minSecond := s[i][1];
      firstOfMinSecond := s[i][0];
    }
    i := i + 1;
  }
}
// </vc-code>

