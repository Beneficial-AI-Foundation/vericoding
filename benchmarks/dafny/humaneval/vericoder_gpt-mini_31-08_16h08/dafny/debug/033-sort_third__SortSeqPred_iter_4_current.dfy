method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
method SortSeqPred_impl(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  var n := |s|;
  // copy s into a mutable array b
  var b := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> b[j] == s[j]
  {
    b[i] := s[i];
    i := i + 1;
  }

  // count positions where p is true
  var m := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= m <= n
  {
    if p[i] {
      m := m + 1;
    }
    i := i + 1;
  }

  // collect the indices where p is true, in increasing order
  var idx := new int[m];
  var k := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= k <= m
    invariant forall t :: 0 <= t < k ==> 0 <= idx[t] < n && p[idx[t]]
    invariant forall t1, t2 :: 0 <= t1 < t2 < k ==> idx[t1] < idx[t2]
  {
    if p[i] {
      idx[k] := i;
      k := k + 1;
    }
    i := i + 1;
  }

  // selection sort the elements of b at positions idx[0..m-1]
  k := 0;
  // global invariant that b's multiset equals s's multiset (copy preserved it)
  while k < m
    invariant 0 <= k <= m
    invariant multiset(b[..]) == multiset(s)
    invariant forall r, t :: 0 <= r < k <= t < m ==> b[idx[r]] <= b[idx[t]]
  {
    // find minimal element among positions idx[k..m-1]
    var minpos := k;
    var t := k + 1;
    while t < m
      invariant k+1 <= t <= m
      invariant k <= minpos < m
      invariant forall u :: k <= u < t ==> b[idx[minpos]] <= b[idx[u]]
    {
      if b[idx[t]] < b[idx[minpos]] {
        minpos := t;
      }
      t := t + 1;
    }
    // place the minimum at idx[k] by swapping
    var tmp := b[idx[k]];
    b[idx[k]] := b[idx[minpos]];
    b[idx[minpos]] := tmp;
    k := k + 1;
  }

  sorted := b[..];
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := SortSeqPred_impl(s, p[..]);
}
// </vc-code>

