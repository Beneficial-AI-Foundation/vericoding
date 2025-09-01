

// <vc-helpers>
method BubbleSort(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
  sorted := s;
  var n := |sorted|;
  var swapped := true;
  var k := n;
  while swapped && k > 0
    invariant |sorted| == n
    invariant multiset(s) == multiset(sorted)
    invariant 0 <= k <= n
    invariant forall i :: n - k <= i < n ==> forall j :: 0 <= j < i ==> sorted[j] <= sorted[i]
  {
    swapped := false;
    var i := 1;
    while i < k
      invariant 1 <= i <= k
      invariant |sorted| == n
      invariant multiset(s) == multiset(sorted)
      invariant forall l :: n - k <= l < n ==> forall r :: 0 <= r < l ==> sorted[r] <= sorted[l]
    {
      if sorted[i-1] > sorted[i] {
        var temp := sorted[i-1];
        sorted := sorted[i-1 := sorted[i]];
        sorted := sorted[i := temp];
        swapped := true;
      }
      i := i + 1;
    }
    k := k - 1;
  }
}

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  var to_sort := [];
  var i : int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |to_sort| <= i
  {
    if p[i] {
      to_sort := to_sort + [s[i]];
    }
    i := i + 1;
  }
  var sorted_to_sort := BubbleSort(to_sort);
  var result := [];
  var idx := 0;
  i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant 0 <= idx <= |to_sort|
  {
    if p[i] {
      result := result + [sorted_to_sort[idx]];
      idx := idx + 1;
    } else {
      result := result + [s[i]];
    }
    i := i + 1;
  }
  sorted := result;
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var p := [];
  var i : int := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |p| == i
  {
    p := p + [i % 3 == 0];
    i := i + 1;
  }
  sorted_even := SortSeqPred(a, p);
}
// </vc-code>

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
{
  assume{:axiom} false;
}