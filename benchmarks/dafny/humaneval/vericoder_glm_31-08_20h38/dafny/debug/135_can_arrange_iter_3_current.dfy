

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
  requires forall i
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
  requires forall i
// </vc-code>

