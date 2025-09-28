// <vc-preamble>

predicate ValidInput(arr: seq<int>)
{
    forall i :: 0 <= i < |arr| ==> arr[i] >= 0
}

predicate HasEvenValue(arr: seq<int>)
{
    exists i :: 0 <= i < |arr| && arr[i] % 2 == 0
}

function SmallestEvenValue(arr: seq<int>): int
    requires HasEvenValue(arr)
{
    SmallestEvenValueHelper(arr, 0, -1)
}

function SmallestEvenValueHelper(arr: seq<int>, index: int, current_min: int): int
    requires 0 <= index <= |arr|
    decreases |arr| - index
{
    if index >= |arr| then current_min
    else if arr[index] % 2 == 0 then
        if current_min == -1 || arr[index] < current_min then
            SmallestEvenValueHelper(arr, index + 1, arr[index])
        else
            SmallestEvenValueHelper(arr, index + 1, current_min)
    else
        SmallestEvenValueHelper(arr, index + 1, current_min)
}

function FirstIndexOfValue(arr: seq<int>, value: int): int
    requires exists i :: 0 <= i < |arr| && arr[i] == value
    decreases |arr|
{
    if |arr| > 0 && arr[0] == value then 0
    else 1 + FirstIndexOfValue(arr[1..], value)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): expose ValidInput non-negativity */
lemma ValidInputImpliesNonNegative(arr: seq<int>)
  requires ValidInput(arr)
  ensures forall i :: 0 <= i < |arr| ==> arr[i] >= 0
{
}

// </vc-helpers>

// <vc-spec>
method pluck(arr: seq<int>) returns (result: seq<int>)
    requires ValidInput(arr)
    ensures |arr| == 0 ==> |result| == 0
    ensures !HasEvenValue(arr) ==> |result| == 0
    ensures HasEvenValue(arr) ==> |result| == 2
    ensures |result| == 2 ==> 0 <= result[1] < |arr|
    ensures |result| == 2 ==> arr[result[1]] == result[0]
    ensures |result| == 2 ==> result[0] % 2 == 0
    ensures |result| == 2 ==> forall i :: 0 <= i < |arr| && arr[i] % 2 == 0 ==> result[0] <= arr[i]
    ensures |result| == 2 ==> forall i :: 0 <= i < |arr| && arr[i] % 2 == 0 && arr[i] == result[0] ==> result[1] <= i
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): scan for smallest even and its first index with invariants */
  if |arr| == 0 {
    result := [];
    return;
  }
  var i := 0;
  var found := false;
  var min := 0;
  var minIdx := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant found <==> exists k :: 0 <= k < i && arr[k] % 2 == 0
    invariant found ==> 0 <= minIdx < i
    invariant found ==> arr[minIdx] % 2 == 0 && min == arr[minIdx]
    invariant found ==> forall k :: 0 <= k < i && arr[k] % 2 == 0 ==> min <= arr[k]
    invariant found ==> forall k :: 0 <= k < i && arr[k] % 2 == 0 && arr[k] == min ==> minIdx <= k
    decreases |arr| - i
  {
    if arr[i] % 2 == 0 {
      if !found || arr[i] < min {
        min := arr[i];
        minIdx := i;
        found := true;
      }
    }
    i := i + 1;
  }
  if !found {
    result := [];
  } else {
    result := [min, minIdx];
  }
}
// </vc-code>
