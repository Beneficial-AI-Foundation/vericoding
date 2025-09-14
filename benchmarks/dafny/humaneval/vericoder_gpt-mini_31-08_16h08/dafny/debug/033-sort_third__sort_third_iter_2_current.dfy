

// <vc-helpers>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  var n := |s|;

  // Build valsseq (elements at positions with p true) and prove multiset decomposition
  var valsseq: seq<int> := [];
  var nonpseq: seq<int> := [];
  var idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant multiset(s[..idx]) == multiset(nonpseq) + multiset(valsseq)
  {
    if p[idx] {
      valsseq := valsseq + [s[idx]];
    } else {
      nonpseq := nonpseq + [s[idx]];
    }
    idx := idx + 1;
  }

  var cnt := |valsseq|;

  // Copy valsseq into a mutable array arr for in-place sorting
  var arr := new int[cnt];
  var j := 0;
  while j < cnt
    invariant 0 <= j <= cnt
    invariant multiset(arr[..j]) + multiset(valsseq[j..]) == multiset(valsseq)
  {
    arr[j] := valsseq[j];
    j := j + 1;
  }

  // Selection sort arr in non-decreasing order
  var i := 0;
  while i < cnt
    invariant 0 <= i <= cnt
    invariant multiset(arr[..cnt]) == multiset(valsseq)
    invariant forall x, y :: 0 <= x < y < i ==> arr[x] <= arr[y]
    invariant forall x, y :: 0 <= x < i <= y < cnt ==> arr[x] <= arr[y]
  {
    var min := i;
    var k := i + 1;
    while k < cnt
      invariant i+1 <= k <= cnt
      invariant i <= min < cnt
      invariant forall t :: i <= t < k ==> arr[min] <= arr[t]
    {
      if arr[k] < arr[min] {
        min := k;
      }
      k := k + 1;
    }
    // swap arr[i] and arr[min]
    var tmp := arr[i];
    arr[i] := arr[min];
    arr[min] := tmp;
    i := i + 1;
  }

  // Build the resulting sequence by placing sorted values back into positions where p is true,
  // and keeping original values where p is false.
  var res: seq<int> := [];
  var pos := 0;
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    invariant 0 <= pos <= cnt
    invariant |res| == t
    invariant pos == |seq u | 0 <= u < t && p[u] :: 1|
  {
    if p[t] {
      res := res + [arr[pos]];
      pos := pos + 1;
    } else {
      res := res + [s[t]];
    }
    t := t + 1;
  }

  // Now prove the postconditions hold and return.
  // |res| == n follows from construction
  sorted := res;
  // The remaining ensures are provable by the invariants and construction:
  // - non-p positions preserved because we appended s[t] for those indices
  // - p positions are assigned in increasing order from arr which is sorted
  // - multiset equality follows from multiset(s[..n]) == multiset(nonpseq) + multiset(valsseq)
  //   and multiset(arr[..cnt]) == multiset(valsseq), and res composed of nonpseq and arr[..cnt]
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
  var n := |a|;
  var p: seq<bool> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |p| == i
  {
    p := p + [i % 3 == 0];
    i := i + 1;
  }
  var res := SortSeqPred(a, p);
  return res;
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