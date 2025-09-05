This verification task implements a function that finds the smallest even value in an array of non-negative integers and returns it along with its index. If multiple occurrences of the same smallest even value exist, it should return the one with the smallest index. If no even values exist or the array is empty, it returns an empty list.

The implementation must correctly handle edge cases and maintain loop invariants to prove that the returned result satisfies all the postconditions, including finding the true minimum even value and the earliest index for that value.

// ======= TASK =======
// Given an array of non-negative integers, find the smallest even value and return it along with its index.
// If multiple occurrences of the same smallest even value exist, return the one with the smallest index.
// If no even values exist or the array is empty, return an empty list.

// ======= SPEC REQUIREMENTS =======
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

// ======= HELPERS =======

// ======= MAIN METHOD =======
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
{
    if |arr| == 0 {
        return [];
    }

    var smallest_even: int := -1;
    var smallest_index: int := -1;
    var found_even := false;

    for i := 0 to |arr|
        invariant found_even ==> 0 <= smallest_index < |arr|
        invariant found_even ==> arr[smallest_index] == smallest_even
        invariant found_even ==> smallest_even % 2 == 0
        invariant found_even ==> forall j :: 0 <= j < i && arr[j] % 2 == 0 ==> smallest_even <= arr[j]
        invariant found_even ==> forall j :: 0 <= j < i && arr[j] % 2 == 0 && arr[j] == smallest_even ==> smallest_index <= j
        invariant !found_even ==> forall j :: 0 <= j < i ==> arr[j] % 2 != 0
        invariant found_even <==> exists j :: 0 <= j < i && arr[j] % 2 == 0
    {
        if arr[i] % 2 == 0 {
            if !found_even || arr[i] < smallest_even {
                smallest_even := arr[i];
                smallest_index := i;
                found_even := true;
            } else if arr[i] == smallest_even && i < smallest_index {
                smallest_index := i;
            }
        }
    }

    if !found_even {
        return [];
    }

    return [smallest_even, smallest_index];
}
