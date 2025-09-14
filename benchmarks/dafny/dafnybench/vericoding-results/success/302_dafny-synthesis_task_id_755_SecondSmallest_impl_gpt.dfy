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
  var n := s.Length;
  var m := min(s[..]);
  var i0, j0: int :| 0 <= i0 < n && 0 <= j0 < n && i0 != j0 && s[i0] == min(s[..]) && s[j0] != s[i0];
  assert s[j0] != m;
  var second := s[j0];
  var w := j0;
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant 0 <= w < n
    invariant s[w] == second
    invariant s[w] != m
    invariant forall t :: 0 <= t < k && s[t] != m ==> s[t] >= second
    decreases n - k
  {
    if s[k] != m && s[k] < second {
      second := s[k];
      w := k;
    }
    k := k + 1;
  }
  secondSmallest := second;
  assert i0 != w;
  assert exists i, j :: 0 <= i < n && 0 <= j < n && i != j && s[i] == min(s[..]) && s[j] == secondSmallest;
}
// </vc-code>

