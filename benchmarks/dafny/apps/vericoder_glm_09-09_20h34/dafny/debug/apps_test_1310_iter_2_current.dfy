predicate ValidInput(arr: seq<bv32>)
{
    |arr| > 0
}

predicate IsMaxXorSubarray(arr: seq<bv32>, result: bv32)
    requires ValidInput(arr)
{
    exists i, j :: 0 <= i <= j < |arr| && result == XorRange(arr, i, j) &&
    forall i1, j1 :: 0 <= i1 <= j1 < |arr| ==> 
        (XorRange(arr, i1, j1) as int) <= (result as int)
}

// <vc-helpers>
function XorRange(arr: seq<bv32>, i: int, j: int): bv32
    requires 0 <= i <= j < |arr|
{
    if i == j then arr[i] else XorRange(arr, i, j-1) ^ arr[j]
}

lemma XorRangeProperties(arr: seq<bv32>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k < |arr|
    ensures XorRange(arr, i, k) == XorRange(arr, i, j) ^ XorRange(arr, j+1, k)
{
    if i == j {
        assert XorRange(arr, i, k) == arr[i] ^ XorRange(arr, j+1, k);
    } else {
        calc {
            XorRange(arr, i, k);
            XorRange(arr, i, k-1) ^ arr[k];
            (XorRange(arr, i, j) ^ XorRange(arr, j+1, k-1)) ^ arr[k];
            { XorRangeProperties(arr, j+1, k-1, k); }
            XorRange(arr, i, j) ^ XorRange(arr, j+1, k);
        }
    }
}

method ComputeMaxXor(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
{
    var max := 0;
    for i := 0 to |arr|
        invariant 0 <= i <= |arr|
        invariant exists start, end :: 0 <= start <= end < i && max == XorRange(arr, start, end)
        invariant forall start, end :: 0 <= start <= end < i ==> (XorRange(arr, start, end) as int) <= (max as int)
    {
        var curr := 0;
        for j := i to |arr|
            invariant i <= j <= |arr|
            invariant curr == XorRange(arr, i, j-1)
            invariant forall start, end :: 0 <= start <= end < i ==> (XorRange(arr, start, end) as int) <= (max as int)
            invariant forall k :: i <= k < j ==> (XorRange(arr, i, k) as int) <= (max as int)
        {
            if j < |arr| {
                curr := curr ^ arr[j];
                if curr > max {
                    max := curr;
                }
            }
        }
    }
    result := max;
    
    // Verify the postcondition
    var i, j :| 0 <= i <= j < |arr| && result == XorRange(arr, i, j) && 
        forall i1, j1 :: 0 <= i1 <= j1 < |arr| ==> (XorRange(arr, i1, j1) as int) <= (result as int);
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
{
    var max := 0;
    for i := 0 to |arr|
        invariant 0 <= i <= |arr|
        invariant exists start, end :: 0 <= start <= end < i && max == XorRange(arr, start, end)
        invariant forall start, end :: 0 <= start <= end < i ==> (XorRange(arr, start, end) as int) <= (max as int)
    {
        var curr := 0;
        for j := i to |arr|
            invariant i <= j <= |arr|
            invariant curr == XorRange(arr, i, j-1)
            invariant forall start, end :: 0 <= start <= end < i ==> (XorRange(arr, start, end) as int) <= (max as int)
            invariant forall k :: i <= k < j ==> (XorRange(arr, i, k) as int) <= (max as int)
        {
            if j < |arr| {
                curr := curr ^ arr[j];
                if curr > max {
                    max := curr;
                }
            }
        }
    }
    result := max;
    
    // Verify the postcondition
    var i, j :| 0 <= i <= j < |arr| && result == XorRange(arr, i, j) && 
        forall i1, j1 :: 0 <= i1 <= j1 < |arr| ==> (XorRange(arr, i1, j1) as int) <= (result as int);
}
// </vc-code>

