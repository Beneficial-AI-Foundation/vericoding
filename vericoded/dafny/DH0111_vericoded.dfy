// <vc-preamble>

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
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method move_one_ball(arr: seq<int>) returns (result: bool)
    requires forall i, j :: 0 <= i < j < |arr| ==> arr[i] != arr[j]
    ensures |arr| == 0 ==> result == true
    ensures result == true ==> (|arr| == 0 || exists k :: 0 <= k < |arr| && is_sorted(rotate_right(arr, k)))
    ensures result == false ==> forall k :: 0 <= k < |arr| ==> !is_sorted(rotate_right(arr, k))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): directly check is_sorted instead of comparing with quicksort */
    if |arr| == 0 {
        result := true;
        return;
    }
    
    var k := 0;
    result := false;
    
    while k < |arr|
        invariant 0 <= k <= |arr|
        invariant result == false ==> forall j :: 0 <= j < k ==> !is_sorted(rotate_right(arr, j))
        invariant result == true ==> exists j :: 0 <= j < k && is_sorted(rotate_right(arr, j))
    {
        var rotated := rotate_right(arr, k);
        
        if is_sorted(rotated) {
            result := true;
            return;
        }
        
        k := k + 1;
    }
}
// </vc-code>
