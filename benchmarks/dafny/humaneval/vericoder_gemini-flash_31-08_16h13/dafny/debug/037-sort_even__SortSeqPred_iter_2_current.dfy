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
{
  assume{:axiom} false;
}

// <vc-helpers>
function IsPermutation<T>(s1: seq<T>, s2: seq<T>): bool
  reads s1, s2
{
  multiset(s1) == multiset(s2)
}

function CountIf<T>(s: seq<T>, p: T -> bool): int
  reads s
  decreases s
{
  if s == [] then 0 else (if p(s[0]) then 1 else 0) + CountIf(s[1..], p)
}


// A helper function to swap elements in a sequence
function Swap<T>(s: seq<T>, i: int, j: int): seq<T>
  requires 0 <= i < |s|
  requires 0 <= j < |s|
{
  if i == j then s
  else s[0..i] + s[j] + s[i + 1 .. j] + s[i] + s[j + 1 ..]
}

predicate IsSorted<T>(s: seq<T>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall i, j :: lo <= i < j < hi ==> s[i] <= s[j]
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
  var N := |s>;

  var p_indices: seq<int> := [];
  var p_values: seq<int> := [];

  for i := 0 to N - 1
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < |p_indices| ==> p[p_indices[k]] == true && s[p_indices[k]] == p_values[k]
    invariant forall k, l :: 0 <= k < l < |p_indices| ==> p_indices[k] < p_indices[l]
    invariant multiset(p_values) == multiset(s[k] | 0 <= k < i && p[k])
  {
    if p[i] {
      p_indices := p_indices + [i];
      p_values := p_values + [s[i]];
    }
  }

  var sorted_p_values := p_values;
  var K := |sorted_p_values>;

  for i := 0 to K - 2
    invariant 0 <= i <= K - 1
    invariant |sorted_p_values| == K
    invariant forall k, l :: 0 <= k < l < i ==> sorted_p_values[k] <= sorted_p_values[l]
    invariant multiset(sorted_p_values) == multiset(p_values)
  {
    var min_idx_p := i;
    for j := i + 1 to K - 1
      invariant i < j <= K
      invariant |sorted_p_values| == K
      invariant i <= min_idx_p < j
      invariant forall k :: i <= k < j ==> sorted_p_values[min_idx_p] <= sorted_p_values[k]
      invariant multiset(sorted_p_values) == multiset(p_values)
    {
      if sorted_p_values[j] < sorted_p_values[min_idx_p] {
        min_idx_p := j;
      }
    }
    if min_idx_p != i {
      sorted_p_values := Swap(sorted_p_values, i, min_idx_p);
    }
  }

  sorted := s;

  var current_p_idx := 0;
  for i := 0 to N - 1
    invariant 0 <= i <= N
    invariant 0 <= current_p_idx <= K
    invariant forall k :: 0 <= k < i && !p[k] ==> sorted[k] == s[k]
    invariant forall k :: 0 <= k < current_p_idx ==> p_indices[k] < i
    invariant multiset(s) == multiset(sorted)
    invariant forall k, l :: 0 <= k < l < current_p_idx ==> sorted_p_values[k] <= sorted_p_values[l]
    invariant forall k :: 0 <= k < i && p[k] ==> exists idx :: 0 <= idx < current_p_idx && p_indices[idx] == k && sorted[k] == sorted_p_values[idx]
  {
    if p[i] {
      sorted := sorted[0..i] + [sorted_p_values[current_p_idx]] + sorted[i+1..];
      current_p_idx := current_p_idx + 1;
    }
  }
}
// </vc-code>

