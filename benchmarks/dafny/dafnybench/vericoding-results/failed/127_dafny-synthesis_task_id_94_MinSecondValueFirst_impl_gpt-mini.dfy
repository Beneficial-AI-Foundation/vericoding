

// <vc-helpers>
lemma MinIdxIsMin(s: array<seq<int>>, minIdx: int)
  requires s.Length > 0
  requires forall k :: 0 <= k < s.Length ==> |s[k]| >= 2
  requires 0 <= minIdx < s.Length
  requires forall j :: 0 <= j < s.Length ==> s[minIdx][1] <= s[j][1]
{
  var i := minIdx;
  assert 0 <= i < s.Length;
  assert s[minIdx][0] == s[i][0];
  assert forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1];
  // Provide an explicit witness to avoid any indentation/formatting warnings for exists
  assert exists k :: k == minIdx && 0 <= k < s.Length && s[minIdx][0] == s[k][0] && (forall j :: 0 <= j < s.Length ==> s[k][1] <= s[j][1]);
}
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
  var minIdx := 0;
  firstOfMinSecond := s[0][0];
  var i := 1;
  while i < s.Length
    invariant 1 <= i <= s.Length
    invariant 0 <= minIdx < i
    invariant firstOfMinSecond == s[minIdx][0]
    invariant forall j :: 0 <= j < i ==> s[minIdx][1] <= s[j][1]
    decreases s.Length - i
  {
    if s[i][1] < s[minIdx][1] {
      minIdx := i;
      firstOfMinSecond := s[minIdx][0];
    }
    i := i + 1;
  }
  MinIdxIsMin(s, minIdx);
  firstOfMinSecond := s[minIdx][0];
  return;
}
// </vc-code>

