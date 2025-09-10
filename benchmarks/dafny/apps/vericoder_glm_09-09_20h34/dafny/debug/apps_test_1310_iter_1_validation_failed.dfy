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
    if i == j then arr[i]
    else XorRange(arr, i, j-1) ^ arr[j]
}

lemma XorRangeProperties(arr: seq<bv32>, i: int, j: int, k: int)
    requires 0 <= i <= j < k < |arr|
    ensures XorRange(arr, i, k) == XorRange(arr, i, j) ^ XorRange(arr, j+1, k)
{
    if j == i {
        assert XorRange(arr, i, k) == arr[i] ^ XorRange(arr, i+1, k);
    } else {
        calc {
            XorRange(arr, i, k);
            == { assert j < k; }
            XorRange(arr, i, j) ^ XorRange(arr, j+1, k);
        }
    }
}

lemma MaxXorPrefixPossibility(arr: seq<bv32>, i: int, xor_val: bv32)
    requires ValidInput(arr)
    requires 0 <= i < |arr|
    requires xor_val == XorRange(arr, 0, i)
    ensures exists j :: 0 <= j <= i && XorRange(arr, j, i) as int >= xor_val as int
    ensures exists j :: 0 <= j <= i && XorRange(arr, j, i) as int <= xor_val as int
{
    if i == 0 {
        assert xor_val == arr[0];
        assert XorRange(arr, 0, 0) == arr[0];
    } else {
        var prev_xor := XorRange(arr, 0, i-1);
        calc {
            xor_val;
            == { assert xor_val == XorRange(arr, 0, i-1) ^ arr[i]; }
            prev_xor ^ arr[i];
        }
        assume prev_xor as int >= xor_val as int || prev_xor as int <= xor_val as int;
        if prev_xor as int >= xor_val as int {
            assert XorRange(arr, i, i) == arr[i];
            assert exists k :: 0 <= k <= i && XorRange(arr, k, i) as int >= xor_val as int;
        } else {
            assert XorRange(arr, 0, i) == xor_val;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
{
    var max_xor := 0 as bv32;
    var current_xor := 0 as bv32;
    
    for i := 0 to |arr|
        invariant 0 <= i <= |arr|
        invariant current_xor == XorRange(arr, 0, i-1)
        invariant exists k, l :: 0 <= k <= l < i && (max_xor as int) >= (XorRange(arr, k, l) as int)
        invariant forall a, b :: 0 <= a <= b < i ==> (XorRange(arr, a, b) as int) <= (max_xor as int)
    {
        if i > 0 {
            current_xor := current_xor ^ arr[i-1];
            
            var temp_xor := current_xor;
            if temp_xor as int > max_xor as int {
                max_xor := temp_xor;
            }
            
            MaxXorPrefixPossibility(arr, i-1, current_xor);
            
            temp_xor := current_xor;
            for j := 0 to i
                invariant 0 <= j <= i
                invariant temp_xor == XorRange(arr, j, i-1)
                invariant forall k :: j <= k < i ==> (XorRange(arr, k, i-1) as int) <= (max_xor as int)
            {
                if j < i {
                    temp_xor := temp_xor ^ arr[j];
                    if temp_xor as int > max_xor as int {
                        max_xor := temp_xor;
                    }
                }
            }
        }
    }
    result := max_xor;
}
// </vc-code>

