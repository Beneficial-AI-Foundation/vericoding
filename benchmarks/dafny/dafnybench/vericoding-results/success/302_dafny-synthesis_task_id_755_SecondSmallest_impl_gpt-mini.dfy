function MinPair(s: seq<int>) : (r: int)
    requires |s| == 2
    ensures s[0] <= s[1] <==> r == s[0]
    ensures s[0] > s[1] ==> r == s[1] 
{
    if s[0] <= s[1] then s[0] else s[1]
}


function min(s: seq<int>) : (r: int)
    requires |s| >= 2
    ensures forall i :: 0 <= i < |s| ==> r <= s[i]
{
    if |s| == 2 then MinPair(s)
    else MinPair([s[0], min(s[1..])])
}

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method SecondSmallest(s: array<int>) returns (secondSmallest: int)
    requires s.Length >= 2
    // There must be at least 2 different values, a minimum and another one
    requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] != s[i]
    ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] == secondSmallest 
    ensures forall k ::  0 <= k < s.Length && s[k] != min(s[..])  ==>  s[k] >= secondSmallest
// </vc-spec>
// <vc-code>
{
  var m := min(s[..]);
  var idxSecond :| 0 <= idxSecond < s.Length && s[idxSecond] != m;
  secondSmallest := s[idxSecond];
  var k := 0;
  while k < s.Length
    invariant 0 <= k <= s.Length
    invariant 0 <= idxSecond < s.Length && s[idxSecond] == secondSmallest
    invariant s[idxSecond] != m
    invariant forall t :: 0 <= t < k && s[t] != m ==> s[t] >= secondSmallest
    decreases s.Length - k
  {
    if s[k] != m {
      if s[k] < secondSmallest {
        secondSmallest := s[k];
        idxSecond := k;
      }
    }
    k := k + 1;
  }
  ghost var iMin :| 0 <= iMin < s.Length && s[iMin] == m;
  assert iMin != idxSecond;
}
// </vc-code>

