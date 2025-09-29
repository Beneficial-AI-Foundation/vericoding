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
/* helper modified by LLM (iteration 3): Fixed MinEvenValue functions to properly handle even values */
function FirstIndexOfValueHelper(arr: seq<int>, value: int, offset: int): int
    requires exists i :: 0 <= i < |arr| && arr[i] == value
    ensures 0 <= FirstIndexOfValueHelper(arr, value, offset) - offset < |arr|
    ensures arr[FirstIndexOfValueHelper(arr, value, offset) - offset] == value
    ensures forall i :: 0 <= i < FirstIndexOfValueHelper(arr, value, offset) - offset ==> arr[i] != value
    decreases |arr|
{
    if arr[0] == value then offset
    else FirstIndexOfValueHelper(arr[1..], value, offset + 1)
}

function FindFirstEvenIndex(arr: seq<int>, value: int): int
    requires HasEvenValue(arr)
    requires value % 2 == 0
    requires exists i :: 0 <= i < |arr| && arr[i] == value
    ensures 0 <= FindFirstEvenIndex(arr, value) < |arr|
    ensures arr[FindFirstEvenIndex(arr, value)] == value
    ensures forall i :: 0 <= i < FindFirstEvenIndex(arr, value) ==> arr[i] != value
{
    FirstIndexOfValueHelper(arr, value, 0)
}

function MinEvenValue(arr: seq<int>): int
    requires HasEvenValue(arr)
    ensures MinEvenValue(arr) % 2 == 0
    ensures exists i :: 0 <= i < |arr| && arr[i] == MinEvenValue(arr)
    ensures forall i :: 0 <= i < |arr| && arr[i] % 2 == 0 ==> MinEvenValue(arr) <= arr[i]
{
    var firstEven := FindFirstEvenValue(arr, 0);
    MinEvenValueHelper(arr, 0, firstEven)
}

function FindFirstEvenValue(arr: seq<int>, index: int): int
    requires 0 <= index < |arr|
    requires exists i :: index <= i < |arr| && arr[i] % 2 == 0
    ensures FindFirstEvenValue(arr, index) % 2 == 0
    ensures exists i :: index <= i < |arr| && arr[i] == FindFirstEvenValue(arr, index)
    decreases |arr| - index
{
    if arr[index] % 2 == 0 then arr[index]
    else FindFirstEvenValue(arr, index + 1)
}

function MinEvenValueHelper(arr: seq<int>, index: int, current_min: int): int
    requires 0 <= index <= |arr|
    requires current_min % 2 == 0
    requires exists i :: 0 <= i < |arr| && arr[i] == current_min
    requires forall i :: 0 <= i < index && arr[i] % 2 == 0 ==> current_min <= arr[i]
    ensures MinEvenValueHelper(arr, index, current_min) % 2 == 0
    ensures exists i :: 0 <= i < |arr| && arr[i] == MinEvenValueHelper(arr, index, current_min)
    ensures forall i :: 0 <= i < |arr| && arr[i] % 2 == 0 ==> MinEvenValueHelper(arr, index, current_min) <= arr[i]
    decreases |arr| - index
{
    if index >= |arr| then current_min
    else if arr[index] % 2 == 0 && arr[index] < current_min then
        MinEvenValueHelper(arr, index + 1, arr[index])
    else
        MinEvenValueHelper(arr, index + 1, current_min)
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
/* code modified by LLM (iteration 3): Use helper functions for correct computation */
{
  if |arr| == 0 || !HasEvenValue(arr) {
    result := [];
  } else {
    var minEven := MinEvenValue(arr);
    var minIndex := FindFirstEvenIndex(arr, minEven);
    result := [minEven, minIndex];
  }
}
// </vc-code>
