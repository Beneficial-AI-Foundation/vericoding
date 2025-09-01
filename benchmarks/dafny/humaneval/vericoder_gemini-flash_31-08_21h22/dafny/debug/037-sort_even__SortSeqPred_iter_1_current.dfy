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
function method IsPermutation<T>(s1: seq<T>, s2: seq<T>): bool
  reads s1, s2
{
  multiset(s1) == multiset(s2)
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
  var n := |s|;
  var a := s;

  // bubble sort for elements where p[i] is true
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant |a| == n
    invariant forall k :: 0 <= k < i && !p[k] ==> a[k] == s[k]
    invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> a[k] <= a[l]
    invariant IsPermutation(s, a)
  {
    for j := n - 1 downto i + 1
      invariant i + 1 <= j <= n
      invariant |a| == n
      invariant forall k :: 0 <= k < i && !p[k] ==> a[k] == s[k]
      invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> a[k] <= a[l]
      invariant IsPermutation(s, a)
      invariant forall k :: j < k < n && p[k] ==> a[k] >= a[j] // Elements already in place at the end of the unsorted part
      invariant forall k :: j <= k < n && !p[k] ==> a[k] == s[k] // Invariant for non-p elements
    {
      if p[j-1] && p[j] && a[j-1] > a[j] { // Only swap if both p[j-1] and p[j] are true
        a := a[0..j-1] + [a[j]] + [a[j-1]] + a[j+1..n];
      } else if p[j-1] && !p[j] && a[j-1] > s[j] {
        // If p[j] is false, a[j] should be s[j].
        // If p[j-1] is true and a[j-1] > s[j], then swap to maintain sortedness for p-elements up to this point
        // and keep s[j] in its original place.
        a := a[0..j-1] + [s[j]] + [a[j-1]] + a[j+1..n];
      } else if !p[j-1] && p[j] && s[j-1] > a[j] {
        // If p[j-1] is false, a[j-1] should be s[j-1].
        // If p[j] is true and s[j-1] > a[j], then swap to maintain sortedness for p-elements up to this point
        // and keep s[j-1] in its original place.
        a := a[0..j-1] + [a[j]] + [s[j-1]] + a[j+1..n];
      }
    }
  }

  // Restore non-p elements to their original positions if they were moved during sorting
  // Note: The bubble sort above should ideally handle this correctly.
  // The complex swap conditions are an attempt to integrate this, but a simpler
  // bubble sort just on p-elements and then re-inserting non-p elements might be easier to prove.

  // Let's refine the bubble sort to be simpler, only sorting elements where p is true.
  // Then, we'll re-construct the sequence.

  var p_indices: seq<int> := [];
  var p_values: seq<int> := [];

  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < |p_indices| ==> p[p_indices[k]]
    invariant forall k, l :: 0 <= k < l < |p_indices| ==> p_indices[k] < p_indices[l]
    invariant forall k :: 0 <= k < |p_values| ==> p[p_indices[k]]
  {
    if p[i] {
      p_indices := p_indices + [i];
      p_values := p_values + [s[i]];
    }
  }

  var sorted_p_values := p_values;

  // Simple bubble sort on p_values
  for i := 0 to |sorted_p_values| - 1
    invariant 0 <= i <= |sorted_p_values|
    invariant forall k, l :: 0 <= k < l < i ==> sorted_p_values[k] <= sorted_p_values[l]
    invariant IsPermutation(p_values, sorted_p_values)
  {
    for j := |sorted_p_values| - 1 downto i + 1
      invariant i + 1 <= j <= |sorted_p_values|
      invariant forall k, l :: 0 <= k < l < i ==> sorted_p_values[k] <= sorted_p_values[l]
      invariant forall k :: j < k < |sorted_p_values| ==> sorted_p_values[k] >= sorted_p_values[j]
      invariant IsPermutation(p_values, sorted_p_values)
    {
      if sorted_p_values[j-1] > sorted_p_values[j] {
        sorted_p_values := sorted_p_values[0..j-1] + [sorted_p_values[j]] + [sorted_p_values[j-1]] + sorted_p_values[j+1..|sorted_p_values|];
      }
    }
  }

  var current_p_value_index := 0;
  var result: seq<int> := [];
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant |result| == i
    invariant current_p_value_index <= |sorted_p_values|
    invariant forall k :: 0 <= k < i && !p[k] ==> result[k] == s[k]
    invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==>
      var idx_k := 0; while idx_k < |p_indices| && p_indices[idx_k] != k { idx_k := idx_k + 1; }
      var idx_l := 0; while idx_l < |p_indices| && p_indices[idx_l] != l { idx_l := idx_l + 1; }
      result[k] <= result[l]
    invariant multiset(s) == multiset(result + s[i..n]) || (i == n && multiset(s) == multiset(result))
  {
    if p[i] {
      result := result + [sorted_p_values[current_p_value_index]];
      current_p_value_index := current_p_value_index + 1;
    } else {
      result := result + [s[i]];
    }
  }
  sorted := result;
}
// </vc-code>

