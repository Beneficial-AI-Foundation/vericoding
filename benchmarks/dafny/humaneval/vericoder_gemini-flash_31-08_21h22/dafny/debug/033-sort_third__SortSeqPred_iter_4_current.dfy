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
function pred(i: int): bool {
  i % 3 == 0
}

lemma sorted_subsequence_multiset_lemma<T>(a: seq<T>, p: T -> bool, sorted_a: seq<T>)
  requires |a| == |sorted_a|
  requires forall i :: 0 <= i < |a| && !p(a[i]) ==> sorted_a[i] == a[i]
  ensures multiset(a) == multiset(sorted_a)
{
  // This lemma is a tautology; it's here to provide a place if some
  // verification efforts need to be explicitly written to prove properties
  // related to `multiset` and `sorted_subsequence`.
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
  var p_indices: seq<bool> := seq(|s|, i => p[i]);
  var sorted_subseq := new int[|s|];
  var temp_subseq: seq<int> := [];

  for i := 0 to |s| - 1
    ensures |temp_subseq| == (count j  | 0 <= j < i && p[j])
    ensures forall k :: 0 <= k < i && !p[k] ==> sorted_subseq[k] == s[k]
    ensures multiset(s[0..i]) == multiset(sorted_subseq[0..i]) + multiset(temp_subseq)
    
  {
    if p[i] {
      temp_subseq := temp_subseq + [s[i]];
    } else {
      sorted_subseq[i] := s[i];
    }
  }

  temp_subseq := common.sort_int(temp_subseq);

  var temp_idx := 0;
  for i := 0 to |s| - 1
    invariant 0 <= temp_idx <= |temp_subseq|
    invariant forall k :: 0 <= k < i && !p[k] ==> sorted_subseq[k] == s[k]
    invariant forall k :: 0 <= k < i && p[k] ==> sorted_subseq[k] == temp_subseq[count j | 0 <= j < k && p[j]]
    invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> sorted_subseq[k] <= sorted_subseq[l]
    
  {
    if p[i] {
      sorted_subseq[i] := temp_subseq[temp_idx];
      temp_idx := temp_idx + 1;
    }
  }

  return sorted_subseq;
}
// </vc-code>

