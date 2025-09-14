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
    ensures XorRange(arr, i, j) == if i == j then arr[i] else arr[i] ^ XorRange(arr, i + 1, j)
{
    if i == j then arr[i] else arr[i] ^ XorRange(arr, i + 1, j)
}

function PSumXor(arr: seq<bv32>, k: int): bv32
    requires 0 <= k < |arr|
    ensures PSumXor(arr, k) == XorRange(arr, 0, k)
{
    if k == 0 then arr[0] else arr[k] ^ PSumXor(arr, k - 1)
}


lemma XorRangePrefixSum(arr: seq<bv32>, i: int, j: int)
    requires 0 <= i <= j < |arr|
    ensures XorRange(arr, i, j) == (if i == 0 then PSumXor(arr, j) else PSumXor(arr, i - 1) ^ PSumXor(arr, j))
{
    if i == 0 {
        calc {
            XorRange(arr, 0, j);
            PSumXor(arr, j);
        }
    } else {
        calc {
            XorRange(arr, i, j);
            arr[i] ^ XorRange(arr, i + 1, j);
            {
                if i + 1 <= j {
                    XorRangePrefixSum(arr, i + 1, j);
                }
            }
            arr[i] ^ (PSumXor(arr, i) ^ PSumXor(arr, j));
            {
                assert XorRange(arr, i + 1, j) == (PSumXor(arr, i) ^ PSumXor(arr, j));
                assert arr[i] ^ PSumXor(arr, i - 1) == PSumXor(arr, i);
                assert arr[i] == (PSumXor(arr, i) ^ PSumXor(arr, i - 1));
            }
            (PSumXor(arr, i) ^ PSumXor(arr, i - 1)) ^ (PSumXor(arr, i) ^ PSumXor(arr, j));
            PSumXor(arr, i - 1) ^ PSumXor(arr, j);
        }
    }
}

lemma XOR_Identity(x: bv32)
    ensures x ^ x == 0bv32
{}

lemma MaxSubarrayXorRangeProperty(arr: seq<bv32>, i: int, j: int, k: int, l: int)
    requires 0 <= i <= j < |arr|
    requires 0 <= k <= l < |arr|
    ensures (XorRange(arr, i, j) as int) <= (XorRange(arr, k, l) as int) ==> !((XorRange(arr, i, j) as int) > (XorRange(arr, k, l) as int))
{}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
{
    var max_xor: bv32 := 0bv32;

    var i: int := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant forall i_iter, j_iter :: 0 <= i_iter <= j_iter < i ==> (XorRange(arr, i_iter, j_iter) as int) <= (max_xor as int)
        invariant i == 0 ==> max_xor == 0bv32
        invariant i > 0 ==> exists ii, jj :: 0 <= ii <= jj < i && max_xor == XorRange(arr, ii, jj)
    {
        var j: int := i;
        while j < |arr|
            invariant i <= j <= |arr|
            invariant forall i_iter, j_iter :: ((0 <= i_iter < i) || (i_iter == i && i_iter <= j_iter < j)) ==> (XorRange(arr, i_iter, j_iter) as int) <= (max_xor as int)
            invariant (i == 0 && j == 0) ==> max_xor == 0bv32
            invariant (i > 0 || j > 0) ==> exists ii, jj :: 0 <= ii <= jj < |arr| && (ii <= i && jj < j || ii < i && jj < |arr|) && max_xor == XorRange(arr, ii, jj)
        {
            var current_xor: bv32 := XorRange(arr, i, j);

            if (current_xor as int) > (max_xor as int) {
                max_xor := current_xor;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    result := max_xor;
}
// </vc-code>

