Given an array of unique integers, determine if it's possible to sort the array in non-decreasing order using only right shift operations. A right shift moves all elements one position to the right, with the last element moving to the first. The method should return True if the array is sortable via rotations, False otherwise, with empty arrays returning True.

// ======= TASK =======
// Given an array of unique integers, determine if it's possible to sort the array
// in non-decreasing order using only right shift operations. A right shift moves
// all elements one position to the right, with the last element moving to the first.
// Return True if sortable, False otherwise. Empty arrays return True.

// ======= SPEC REQUIREMENTS =======
predicate is_sorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function rotate_right(arr: seq<int>, k: int): seq<int>
    requires 0 <= k <= |arr|
    ensures |rotate_right(arr, k)| == |arr|
{
    if |arr| == 0 then arr
    else if k == 0 then arr
    else arr[|arr|-k..] + arr[..|arr|-k]
}

// ======= HELPERS =======
method quicksort(s: seq<int>) returns (sorted: seq<int>)
    decreases |s|
{
    if |s| <= 1 {
        sorted := s;
    } else {
        var pivot := s[0];
        var smaller := [];
        var greater := [];

        var i := 1;
        while i < |s|
            invariant 1 <= i <= |s|
            invariant |smaller| + |greater| == i - 1
            invariant |smaller| < |s|
            invariant |greater| < |s|
        {
            if s[i] < pivot {
                smaller := smaller + [s[i]];
            } else {
                greater := greater + [s[i]];
            }
            i := i + 1;
        }

        var sorted_smaller := quicksort(smaller);
        var sorted_greater := quicksort(greater);
        sorted := sorted_smaller + [pivot] + sorted_greater;
    }
}

// <vc-helpers>
// </vc-helpers>

// ======= MAIN METHOD =======
method move_one_ball(arr: seq<int>) returns (result: bool)
    requires forall i, j :: 0 <= i < j < |arr| ==> arr[i] != arr[j]
    ensures |arr| == 0 ==> result == true
    ensures result == true ==> (|arr| == 0 || exists k :: 0 <= k < |arr| && is_sorted(rotate_right(arr, k)))
    ensures result == false ==> forall k :: 0 <= k < |arr| ==> !is_sorted(rotate_right(arr, k))
{
    if |arr| == 0 {
        result := true;
        return;
    }

    var rotations := 0;
    while rotations < |arr|
        invariant 0 <= rotations <= |arr|
        invariant forall k :: 0 <= k < rotations ==> !is_sorted(rotate_right(arr, k))
    {
        if is_sorted(rotate_right(arr, rotations)) {
            result := true;
            return;
        }
        rotations := rotations + 1;
    }

    result := false;
}
