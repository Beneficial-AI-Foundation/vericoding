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
    ensures XorRange(arr, i, k) == XorRange(arr, i, j-1) ^ XorRange(arr, j, k)
{
    if j == i {
        calc {
            XorRange(arr, i, k);
            XorRange(arr, i, i) ^ XorRange(arr, i+1, k);
            { assert XorRange(arr, i, i) == arr[i]; }
            arr[i] ^ XorRange(arr, i+1, k);
            XorRange(arr, i, k);
        }
    } else {
        calc {
            XorRange(arr, i, k);
            XorRange(arr, i, j-1) ^ XorRange(arr, j, k);
            == { XorRangeProperties(arr, i, j-1, k); }
            XorRange(arr, i, j-1) ^ (XorRange(arr, j, j) ^ XorRange(arr, j+1, k));
            == { assert XorRange(arr, j, j) == arr[j]; }
            XorRange(arr, i, j-1) ^ arr[j] ^ XorRange(arr, j+1, k);
            == { assert XorRange(arr, i, j) == XorRange(arr, i, j-1) ^ arr[j]; }
            XorRange(arr, i, j) ^ XorRange(arr, j+1, k);
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
function XorRange(arr: seq<bv32>, i: int, j: int): bv32
    requires 0 <= i <= j < |arr|
{
    if i == j then arr[i] else XorRange(arr, i, j-1) ^ arr[j]
}

lemma XorRangeProperties(arr: seq<bv32>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k < |arr|
    ensures XorRange(arr, i, k) == XorRange(arr, i, j-1) ^ XorRange(arr, j, k)
{
    if j == i {
        calc {
            XorRange(arr, i, k);
            XorRange(arr, i, i) ^ XorRange(arr, i+1, k);
            { assert XorRange(arr, i, i) == arr[i]; }
            arr[i] ^ XorRange(arr, i+1, k);
            XorRange(arr, i, k);
        }
    } else {
        calc {
            XorRange(arr, i, k);
            XorRange(arr, i, j-1) ^ XorRange(arr, j, k);
            == { XorRangeProperties(arr, i, j-1, k); }
            XorRange(arr, i, j-1) ^ (XorRange(arr, j, j) ^ XorRange(arr, j+1, k));
            == { assert XorRange(arr, j, j) == arr[j]; }
            XorRange(arr, i, j-1) ^ arr[j] ^ XorRange(arr, j+1, k);
            == { assert XorRange(arr, i, j) == XorRange(arr, i, j-1) ^ arr[j]; }
            XorRange(arr, i, j) ^ XorRange(arr, j+1, k);
// </vc-code>

