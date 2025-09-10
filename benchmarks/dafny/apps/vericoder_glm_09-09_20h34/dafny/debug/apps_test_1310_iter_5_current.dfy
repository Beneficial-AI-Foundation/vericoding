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
    decreases j - i
{
    if i == j then 
        arr[i] 
    else 
        arr[i] xor XorRange(arr, i+1, j)
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
{
    var max: bv32 := arr[0];
    for i := 0 to |arr|-1
    {
        var current: bv32 := 0;
        for j := i to |arr|-1
        {
            current := current xor arr[j];
            if (current as int) > (max as int) then
                max := current;
        }
    }
    return max;
}
// </vc-code>

