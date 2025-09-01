

// <vc-helpers>
predicate sorted_by_predicate(s: seq<int>, p: seq<bool>)
  requires |s| == |p|
{
  forall i, j :: 0 <= i < j < |s| && p[i] && p[j] ==> s[i] <= s[j]
}

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures sorted_by_predicate(sorted, p)
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  var result := s;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == |s|
    invariant multiset(s) == multiset(result)
    invariant forall k :: 0 <= k < |s| && !p[k] ==> result[k] == s[k]
    invariant sorted_by_predicate(result[..i], p[..i])
    invariant forall k :: i <= k < |s| ==> (p[k] ==> multiset({result[k]}) <= multiset({s[k]}))
            && (!p[k] ==> result[k] == s[k]);
    invariant forall k, l :: 0 <= k < i && i <= l < |s| && p[k] && p[l] ==> result[k] <= result[l]
  {
    if p[i] {
      var j := i;
      var min_val := result[i];
      var min_idx := i;
      while j < |s|
        invariant i <= j <= |s|
        invariant |result| == |s|
        invariant multiset(s) == multiset(result)
        invariant forall k :: 0 <= k < |s| && !p[k] ==> result[k] == s[k]
        invariant p[i] ==> (p[min_idx] && result[min_idx] == min_val)
        invariant forall k :: i <= k < j && p[k] ==> min_val <= result[k]
        invariant forall k, l :: 0 <= k < i && i <= l < |s| && p[k] && p[l] ==> result[k] <= result[l]
        invariant forall k, l :: 0 <= k < i && l < i && p[k] && p[l] ==> result[k] <= result[l]
        invariant forall x, y :: 0 <= x < i && i <= y < |s| && !p[x] ==> result[x] == s[x]
      {
        if p[j] && result[j] < min_val {
          min_val := result[j];
          min_idx := j;
        }
        j := j + 1;
      }
      if min_idx != i {
        result := result[min_idx := result[i]];
        result := result[i := min_val];
      }
    }
    i := i + 1;
  }
  return result;
}
// </vc-helpers>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var p: seq<bool> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |p| == i
    decreases |a| - i
  {
    p := p + [(i % 2 == 0)];
    i := i + 1;
  }

  var sorted_result := SortSeqPred(a, p);

  return sorted_result;
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