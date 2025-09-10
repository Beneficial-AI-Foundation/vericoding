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
    var current_psxor: bv32 := 0bv32;
    var prefix_xors: set<bv32> := {0bv32}; // Stores all possible prefix XOR sums up to the current index

    // The maximum XOR subarray can be found by iterating through all possible right endpoints
    // and for each right endpoint, finding a left endpoint such that the XOR sum is maximized.
    // This can be done efficiently by maintaining a set of all prefix XOR sums encountered so far.
    // Given the current prefix XOR sum `current_psxor` (equivalent to PSumXor(arr, k) or XorRange(arr, 0, k)),
    // we want to find a previous prefix XOR sum `prev_psxor` (equivalent to PSumXor(arr, i-1) or 0bv32)
    // such that `current_psxor ^ prev_psxor` is maximized.
    // This `current_psxor ^ prev_psxor` represents `XorRange(arr, i, k)`.

    // The maximum XOR subarray will always be non-negative because (XOR_Identity(x) provides x ^ x == 0,
    // and if all values are 0, then the maximum is 0. If some values are non-zero,
    // then the maximum XOR can be greater than 0. The smallest possible bv32 value is 0.
    // A single element subarray is always possible, and if arr[k] > 0, then the max_xor can be 0.

    // Initialize max_xor with the largest possible value obtained from a single element subarray or 0.
    // Since bv32 is unsigned, 0bv32 is the smallest possible value.
    // The problem asks for the maximum XOR subarray.

    // A simple approach is to iterate all possible i and j, calculate XorRange(arr, i, j) and update max_xor.
    // This is O(N^2). Since the problem is likely on small N or requires bit manipulation for larger N,
    // let's try the O(N^2) approach first for simplicity, then optimize if needed.

    // Given the small memory limit for helpers, this approach is more likely to pass.
    // Iterate through all possible i (start index)
    var i: int := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant exists i_curr, j_curr :: 0 <= i_curr <= j_curr < i && (max_xor as int) == (XorRange(arr, i_curr, j_curr) as int) || i == 0
        invariant forall i_iter, j_iter :: 0 <= i_iter <= j_iter < i ==> (XorRange(arr, i_iter, j_iter) as int) <= (max_xor as int)
    {
        // Iterate through all possible j (end index), starting from i
        var j: int := i;
        while j < |arr|
            invariant i <= j <= |arr|
            invariant exists i_curr, j_curr :: 0 <= i_curr <= j_curr < j && (max_xor as int) == (XorRange(arr, i_curr, j_curr) as int) || j == i
            invariant forall i_iter, j_iter :: ((i_iter >= i && i_iter <= j) || i_iter < i) && j_iter < j && i_iter <= j_iter ==> (XorRange(arr, i_iter, j_iter) as int) <= (max_xor as int)
            invariant max_xor == (0bv32 as bv32) || exists ii, jj :: 0 <= ii <= jj < j && max_xor == XorRange(arr, ii, jj)
        {
            var current_xor: bv32;
            if i == j {
                current_xor := arr[i];
            } else {
                current_xor := XorRange(arr, i, j);
            }

            if (current_xor as int) > (max_xor as int) {
                max_xor := current_xor;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    // Now prove that max_xor is indeed the maximum.
    // We have iterated through all possible subarrays [i, j].
    // The loop invariants ensure that after the loops complete, max_xor holds the maximum value found among all subarrays.

    result := max_xor;
}
// </vc-code>

