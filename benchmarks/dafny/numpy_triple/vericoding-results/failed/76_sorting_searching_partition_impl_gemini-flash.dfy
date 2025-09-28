// <vc-preamble>
// Ghost predicate to check if a sequence is sorted in non-decreasing order
ghost predicate IsSorted(s: seq<real>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Ghost predicate to check if two sequences are permutations of each other
ghost predicate IsPermutation(s1: seq<real>, s2: seq<real>)
{
    |s1| == |s2| &&
    forall x :: Count(s1, x) == Count(s2, x)
}

// Ghost function to count occurrences of an element in a sequence
ghost function Count(s: seq<real>, x: real): nat
{
    if |s| == 0 then 0
    else (if s[0] == x then 1 else 0) + Count(s[1..], x)
}

// Ghost function that returns a sorted version of the input sequence
ghost function SortedVersion(s: seq<real>): seq<real>

// Ghost predicate that ensures SortedVersion produces a valid sorted permutation
ghost predicate SortedVersionValid(s: seq<real>)
{
    var sorted := SortedVersion(s);
    IsSorted(sorted) && IsPermutation(s, sorted)
}

// Axiom that SortedVersion always produces a valid result
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed parse error by adding closing parenthesis. */
function get_partitioned_elements(s: seq<real>, pivot_val: real): (less: seq<real>, greater_equal: seq<real>)
{
  var less_elements: seq<real> := [];
  var greater_equal_elements: seq<real> := [];

  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant forall x :: x in less_elements ==> x < pivot_val
    invariant forall x :: x in greater_equal_elements ==> x >= pivot_val
  {
    if s[i] < pivot_val {
      less_elements := less_elements + [s[i]];
    }
    else {
      greater_equal_elements := greater_equal_elements + [s[i]];
    }
  }
  return (less_elements, greater_equal_elements);
}

// </vc-helpers>

// <vc-spec>
lemma {:axiom} SortedVersionIsValid(s: seq<real>)
    ensures SortedVersionValid(s)

/**
 * Partitions an array around the k-th element.
 * Returns a rearranged copy where the k-th element is in its correct sorted position,
 * with smaller elements before it and equal/greater elements after it.
 */
method Partition(arr: seq<real>, kth: int) returns (result: seq<real>)
    requires 0 <= kth < |arr|
    ensures |result| == |arr|
    // All elements before kth position are <= the kth element
    ensures forall i :: 0 <= i < kth ==> result[i] <= result[kth]
    // All elements after kth position are >= the kth element
    ensures forall i :: kth < i < |result| ==> result[i] >= result[kth]
    // The k-th element is in its correct sorted position
    ensures SortedVersionValid(arr) ==> result[kth] == SortedVersion(arr)[kth]
    // The result is a permutation of the original array
    ensures IsPermutation(arr, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simplified the implementation by using only `get_partitioned_elements` helper and then carefully reconstructing the result based on count of elements, fixing `for` loop syntax errors. */
{
  var pivot_val := arr[kth];
  var (less_sub_seq, greater_equal_sub_seq) := get_partitioned_elements(arr, pivot_val);

  var num_less_than_pivot := |less_sub_seq|;

  var elements_equal_to_pivot: seq<real> := [];
  for x in arr {
    if x == pivot_val {
      elements_equal_to_pivot := elements_equal_to_pivot + [x];
    }
  }
  var num_equal_to_pivot := |elements_equal_to_pivot|;

  result := [];

  // Add elements strictly less than pivot_val
  result := result + less_sub_seq;

  // Add elements equal to pivot_val until the kth position is reached
  var pivots_added_so_far := 0;
  while |result| < kth && pivots_added_so_far < num_equal_to_pivot {
    result := result + [pivot_val];
    pivots_added_so_far := pivots_added_so_far + 1;
  }

  // Add the remaining elements equal to pivot_val into the greater_equal_part
  var remaining_equal_elements: seq<real> := [];
  while pivots_added_so_far < num_equal_to_pivot {
    remaining_equal_elements := remaining_equal_elements + [pivot_val];
    pivots_added_so_far := pivots_added_so_far + 1;
  }

  // Filter out elements that were equal to pivot_val from greater_equal_sub_seq
  var greater_than_pivot_sub_seq: seq<real> := [];
  for x in greater_equal_sub_seq {
    if x != pivot_val {
      greater_than_pivot_sub_seq := greater_than_pivot_sub_seq + [x];
    }
  }

  result := result + remaining_equal_elements + greater_than_pivot_sub_seq;

  // The issue is that get_partitioned_elements puts all equal elements in greater_equal_sub_seq.
  // We need to distribute them around the kth index correctly. Since we already have the `less` elements,
  // we know where the pivot element should roughly lie. We need to take elements that are exactly `pivot_val`
  // and filter them out from `greater_equal_sub_seq` to place them correctly.

  var final_result: seq<real> := [];
  var elements_to_place_after_kth: seq<real> := [];

  // Add all elements < pivot_val
  final_result := final_result + less_sub_seq;

  // Place elements == pivot_val
  var num_pivots_already_placed := 0;
  // Place pivot elements until the current length reaches kth
  while |final_result| < kth && num_pivots_already_placed < num_equal_to_pivot {
    final_result := final_result + [pivot_val];
    num_pivots_already_placed := num_pivots_already_placed + 1;
  }
  
  // Place the actual kth pivot if it hasn't been placed yet
  if |final_result| == kth {
      if num_pivots_already_placed < num_equal_to_pivot {
          final_result := final_result + [pivot_val];
          num_pivots_already_placed := num_pivots_already_placed + 1;
      } else if (num_equal_to_pivot == 0 && ArrHasPivotValue(arr, pivot_val)) {
        // This case handles if the arr[kth] is the only pivot_val
        final_result := final_result + [pivot_val];
      }
  }

  // Add any remaining pivot values to the part that comes after kth
  while num_pivots_already_placed < num_equal_to_pivot {
    elements_to_place_after_kth := elements_to_place_after_kth + [pivot_val];
    num_pivots_already_placed := num_pivots_already_placed + 1;
  }

  // Add elements > pivot_val (from greater_equal_sub_seq after removing pivot_val)
  var only_greater_than_pivot: seq<real> := [];
  for x in greater_equal_sub_seq {
    if x != pivot_val {
      only_greater_than_pivot := only_greater_than_pivot + [x];
    }
  }
  elements_to_place_after_kth := elements_to_place_after_kth + only_greater_than_pivot;

  result := final_result + elements_to_place_after_kth;
}

ghost predicate ArrHasPivotValue(arr: seq<real>, pivot_val: real)
{
    exists i :: 0 <= i < |arr| && arr[i] == pivot_val
}
// </vc-code>
