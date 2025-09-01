```vc-helpers
function method Multiset(s: seq<int>): multiset<int> {
  multiset(s)
}

function method Predicate(i: int): bool {
  i % 3 == 0
}

predicate IsSortedPredicate(s: seq<int>, p: int -> bool)
{
    forall i, j :: 0 <= i < j < |s| && p(i) && p(j) ==> s[i] <= s[j]
}

predicate IsUnchangedPredicate(s_orig: seq<int>, s_curr: seq<int>, p: int -> bool)
{
    forall i :: 0 <= i < |s_orig| && !p(i) ==> s_orig[i] == s_curr[i]
}
```

```vc-code
{
  var n := |a>;
  var p_arr := new seq<bool>(n, i => i % 3 == 0);
  
  var sorted_even_arr := new int[n];
  var selected_elements: seq<int> := [];
  var selected_indices: seq<int> := [];

  // Collect elements where predicate is true
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i && p_arr[k] ==> k in selected_indices
    invariant forall k :: 0 <= k < i && p_arr[k] ==> a[k] in selected_elements
    invariant |selected_elements| == |selected_indices|
  {
    if p_arr[i] {
      selected_elements := selected_elements + [a[i]];
      selected_indices := selected_indices + [i];
    }
  }

  // Sort the collected elements
  selected_elements := SortSeq(selected_elements);

  // Fill the result array
  var selected_counter := 0;
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant selected_counter <= |selected_elements|
    invariant forall k :: 0 <= k < i && !p_arr[k] ==> sorted_even_arr[k] == a[k]
    invariant forall k :: 0 <= k < i && p_arr[k] ==> sorted_even_arr[k] == selected_elements[var_index_of_selected_element_at_k(k, selected_indices)]
    invariant forall k :: 0 <= k < i && p_arr[k] ==> 0 <= var_index_of_selected_element_at_k(k, selected_indices) < |selected_elements|
    invariant forall k, l :: 0 <= k < l < selected_counter ==> selected_elements[k] <= selected_elements[l]
    invariant forall k :: 0 <= k < i && p_arr[k] ==> Multiset(selected_elements[..selected_counter]) <= Multiset(a)
    decreases n - i
  {
    if p_arr[i] {
      sorted_even_arr[i] := selected_elements[selected_counter];
      selected_counter := selected_counter + 1;
    } else {
      sorted_even_arr[i] := a[i];
    }
  }
  
  // Prove final postconditions
  sorted_even := sorted_even_arr;
  
  assert |sorted_even| == |a|;
  assert IsSortedPredicate(sorted_even, Predicate);
  assert IsUnchangedPredicate(a, sorted_even, Predicate);
  assert Multiset(a) == Multiset(sorted_even); // This relies on the property that selected elements are replaced in order and non-selected elements are preserved.

  return sorted_even;
}

// Helper function to find the index of an original element within the `selected_elements` list
// This is used in the loop invariant to refer to the correctly placed sorted element.
function var_index_of_selected_element_at_k(k: int, selected_indices: seq<int>): int
  requires 0 <= k < |selected_indices|
  reads selected_indices
  decreases k
{
  var_index_of_selected_element_at_k_helper(k, selected_indices, 0)
}

function var_index_of_selected_element_at_k_helper(k: int, selected_indices: seq<int>, current_index: int): int
  requires 0 <= k < |selected_indices|
  requires 0 <= current_index <= k
  reads selected_indices
  decreases k - current_index
{
  if current_index == k then
    0
  else
    1 + var_index_of_selected_element_at_k_helper(k, selected_indices, current_index + 1)
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
{
  if |s| <= 1 {
    return s;
  } else {
    var pivot := s[|s| / 2];
    var less: seq<int> := [];
    var equal: seq<int> := [];
    var greater: seq<int> := [];

    for i := 0 to |s| - 1 {
      if s[i] < pivot {
        less := less + [s[i]];
      } else if s[i] == pivot {
        equal := equal + [s[i]];
      } else {
        greater := greater + [s[i]];
      }
    }
    
    var sorted_less := SortSeq(less);
    var sorted_greater := SortSeq(greater);
    return sorted_less + equal + sorted_greater;
  }
}
```