

// <vc-helpers>
lemma helper_lemma(arr: seq<int>, x: int)
  requires 1 <= x < |arr|
  requires forall i :: 1 <= i < x ==> arr[i] >= arr[i-1]
  requires arr[x] >= arr[x-1]
  ensures forall i :: 1 <= i <= x ==> arr[i] >= arr[i-1]
{
  if x == 1 {
  } else {
    calc {
      forall i :: 1 <= i <= x ==> arr[i] >= arr[i-1];
    == { assert forall i :: 1 <= i < x ==> arr[i] >= arr[i-1]; }
      (arr[x] >= arr[x-1]) && (forall i :: 1 <= i < x ==> arr[i] >= arr[i-1]);
    }
    helper_lemma(arr, x-1);
  }
}

lemma helper_lemma_two(arr: seq<int>, x: int)
  requires 1 <= x < |arr|
  requires forall i :: x < i < |arr| ==> arr[i] >= arr[i-1]
  ensures forall i :: x <= i < |arr| ==> arr[i] >= arr[i-1]
{
  if x == |arr| - 1 {
  } else {
    assert forall i :: x < i < |arr| ==> arr[i] >= arr[i-1];
    helper_lemma_two(arr, x+1);
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
  var i := 1;
  while i < |arr|
    invariant 1 <= i <= |arr|
    invariant forall j :: 0 < j < i ==> arr[j] >= arr[j-1]
  {
    if arr[i] < arr[i-1] {
      return i;
    }
    i := i + 1;
  }
  return -1;
}
// </vc-code>

