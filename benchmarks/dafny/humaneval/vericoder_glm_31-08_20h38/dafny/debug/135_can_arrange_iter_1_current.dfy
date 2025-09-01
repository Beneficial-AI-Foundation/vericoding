

// <vc-helpers>
lemma helper_lemma(arr: seq<int>, x: int)
  requires 1 <= x < |arr|
  requires arr[x] >= arr[x - 1]
  ensures forall i :: 0 < i <= x ==> arr[i] >= arr[i - 1]
{
  if x == 1 {
  } else {
    calc {
      forall i :: 0 < i <= x ==> arr[i] >= arr[i - 1];
    == { assert forall i :: 0 < i < x ==> arr[i] >= arr[i - 1]; }
      (arr[x] >= arr[x - 1]) && (forall i :: 0 < i < x ==> arr[i] >= arr[i - 1]);
    }
    helper_lemma(arr, x - 1);
  }
}

lemma helper_lemma_two(arr: seq<int>, x: int)
  requires 1 <= x < |arr|
  requires arr[x] < arr[x - 1]
  ensures forall i :: 0 < i <= x ==> (i == x || arr[i] >= arr[i - 1])
{
  if x == 1 {
  } else {
    calc {
      forall i :: 0 < i <= x ==> (i == x || arr[i] >= arr[i - 1]);
    == { assert forall i :: 0 < i < x ==> arr[i] >= arr[i - 1]; }
      (arr[x] < arr[x - 1]) && (forall i :: 0 < i < x ==> arr[i] >= arr[i - 1]);
    }
    helper_lemma(arr, x - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method can_arrange(arr: seq<int>) returns (pos: int)
  // pre-conditions-start
  requires |arr| > 0
  requires forall i, j :: 0 <= i < j < |arr| ==> arr[i] != arr[j]
  // pre-conditions-end
  // post-conditions-start
  ensures pos == -1 ==> forall i :: 1 <= i < |arr| ==> arr[i] >= arr[i - 1]
  ensures pos >= 0 ==> 1 <= pos < |arr| && arr[pos] < arr[pos - 1]
  ensures pos >= 0 ==> forall i :: pos < i < |arr| ==> arr[i] >= arr[i - 1]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var N := |arr|;
  if N == 1 {
    return -1;
  }

  var i := 1;
  var found_idx := -1;

  while i < N
    // Loop Invariant 1
    invariant 0 <= i <= N
    // Loop Invariant 2
    invariant found_idx == -1 ==> forall j :: 1 <= j < i ==> arr[j] >= arr[j - 1]
    // Loop Invariant 3
    invariant found_idx >= 0 ==> 1 <= found_idx < i && arr[found_idx] < arr[found_idx - 1]
    // Loop Invariant 4
    invariant found_idx >= 0 ==> forall j :: found_idx < j < i ==> arr[j] >= arr[j - 1]
    // Loop Invariant for Termination
    decreases N - i
  {
    if arr[i] < arr[i - 1] {
      if (found_idx == -1) {
        found_idx := i;
        helper_lemma_two(arr, found_idx);
      } else {
        helper_lemma(arr, i);
      }
    } else {
      if (found_idx == -1) {
        helper_lemma(arr, i);
      } else {
        helper_lemma(arr, i);
      }
    }
    i := i + 1;
  }
  return found_idx;
}
// </vc-code>

