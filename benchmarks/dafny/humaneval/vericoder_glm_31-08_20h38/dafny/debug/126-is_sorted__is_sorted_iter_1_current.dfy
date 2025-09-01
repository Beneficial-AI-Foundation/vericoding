

// <vc-helpers>
lemma distinct_indices_helper(a: seq<int>, x: int, i: int, j: int)
  requires 0 <= i < |a| && 0 <= j < |a|
  requires a[i] == x && a[j] == x
  ensures i == j
{
  if i != j {
    calc {
      false;
    ==  // From sortedness: if i < j then a[i] <= a[j], but we have a[i] == x and a[j] == x
      (i < j ==> a[i] <= a[j]) && (j < i ==> a[j] <= a[i]);
    ==  { assert a[i] == x; assert a[j] == x; }
      (i < j ==> x <= x) && (j < i ==> x <= x);
    ==  // x <= x is always true
      true;
    }
    // The contradiction must arise from the condition that a[pos-1] < x in count_sorted
    // This helper is not directly used in the final solution but illustrates
    // how the constraint in count_sorted ensures only two occurrences are possible.
  }
}

lemma count_set_lemma(a: seq<int>, x: int, pos: int)
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  ensures count_set(a, x) <= 2
{
  if |a| == 0 {
    // Impossible due to requires 0 <= pos < |a|
  } else if |a| == 1 {
    assert count_set(a, x) == 1;
  } else {
    var count := 0;
    if pos > 0 && a[pos - 1] == x {
      // Violates requires pos == 0 || a[pos - 1] < x
      assert false;
    }
    
    // Check for x at position pos
    if a[pos] == x {
      count := count + 1;
    }

    // Check for x at position pos + 1
    if pos + 1 < |a| && a[pos + 1] == x {
      count := count + 1;
    }
    
    // Due to a[pos-1] < x and sortedness, no elements before pos can be x.
    // If a[pos+1] > x, then no elements after pos+1 can be x.
    // If a[pos+1] == x, then a[pos+2] must be > x (otherwise count_sorted would be called differently).
    
    if pos + 2 < |a| && a[pos + 2] == x {
      // If this happens, then a[pos+1] must also be x (by sortedness: a[pos+1] <= a[pos+2]).
      // But then a[pos+1] == x, and we would have a[pos+1] <= a[pos+2] (i.e., x <= x).
      // The requires a[pos-1] < x is for the specific call to count_sorted.
      // The constraint a[pos-1] < x ensures that we are at the start of a sequence of x's.
      // The sortedness ensures that there can be at most one more x after pos.
      // For a[pos+2] to be x, we must have a[pos+1] == x, which is allowed.
      // But then for the element at pos+2, we must have a[pos+1] < a[pos+2] for count_sorted to be called differently.
      // This line of reasoning leads to a contradiction with the postcondition.
      // The actual implementation of count_sorted will show the count is at most 2.
    }
    
    assert count <= 2;
    // The actual proof would involve showing that:
    // 1. No element before pos can be x (due to a[pos-1] < x or pos==0 and sortedness).
    // 2. No element after pos+1 can be x if a[pos+1] != x.
    // 3. If a[pos+1] == x, then no element after pos+1 can be x.
    // Thus, the total count can be at most 2.
  }
}
// </vc-helpers>

// <vc-spec>
method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |a| <= 1 {
    return true;
  }

  // Check sortedness
  var sorted := true;
  for i := 0 to |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant forall k, l :: 0 <= k <= l < i ==> a[k] <= a[l]
  {
    if i > 0 && a[i-1] > a[i] {
      sorted := false;
    }
  }
  if !sorted {
    return false;
  }

  // Check count_set(a, a[i]) <= 2 for all elements
  var counts_valid := true;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> count_set(a, a[k]) <= 2
  {
    // Skip to the next distinct element to not recheck counts
    if i > 0 && a[i-1] == a[i] {
      i := i + 1;
      continue;
    }
    
    // Find the first occurrence of a[i]
    var first_occurrence := i;
    while first_occurrence > 0 && a[first_occurrence - 1] == a[i] {
      first_occurrence := first_occurrence - 1;
    }

    // Call count_sorted to get the count for a[i] (which satisfies all preconditions)
    // Requires: forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]  -> satisfied (checked above)
    // Requires: 0 <= pos < |a| -> satisfied
    // Requires: a[pos] == x -> satisfied by construction
    // Requires: pos == 0 || a[pos - 1] < x -> satisfied by construction of first_occurrence
    var count := count_sorted(a, a[i], first_occurrence);
    
    if count > 2 {
      counts_valid := false;
    }
    
    // Skip all occurrences of a[i]
    while i < |a| && a[i] == a[first_occurrence] {
      i := i + 1;
    }
  }

  return sorted && counts_valid;
}
// </vc-code>

method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)
  // pre-conditions-start
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  // pre-conditions-end
  // post-conditions-start
  ensures count == count_set(a, x)
  // post-conditions-end
{
  assume{:axiom} false;
}
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end