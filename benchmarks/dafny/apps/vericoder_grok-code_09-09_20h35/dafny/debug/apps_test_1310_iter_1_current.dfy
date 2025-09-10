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
function XorRange(arr: seq<bv32>, i: nat, j: nat): bv32
    requires 0 <= i <= j <= |arr|
{
    if j == i then 0 else (XorRange(arr, i, j-1)) ^ arr[j-1]
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
{
    var result := 0;
    var n := |arr|;
    for i := 0 to n {
        for j := i + 1 to n {
            var xorVal := 0;
            var k := i;
            while k < j
                invariant i <= k <= j
                invariant xorVal == XorRange(arr, i, k)
            {
                xorVal := xorVal ^ arr[k];
                k := k + 1;
            }
            if xorVal > result {
                result := xorVal;
            }
        }
    }
}
// </vc-code>

