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
    if i == j then arr[i]
    else arr[i] ^ XorRange(arr, i+1, j)
}

lemma XorRangeExtend(arr: seq<bv32>, i: int, j: int)
    requires 0 <= i < j < |arr|
    ensures XorRange(arr, i, j) == arr[i] ^ XorRange(arr, i+1, j)
{
    // Follows directly from the definition
}

lemma XorRangeSingle(arr: seq<bv32>, i: int)
    requires 0 <= i < |arr|
    ensures XorRange(arr, i, i) == arr[i]
{
    // Follows directly from the definition
}

lemma XorRangeStep(arr: seq<bv32>, i: int, j: int)
    requires 0 <= i <= j < |arr|
    ensures j == i ==> XorRange(arr, i, j) == arr[i]
    ensures j > i ==> XorRange(arr, i, j) == XorRange(arr, i, j-1) ^ arr[j]
{
    if j == i {
        XorRangeSingle(arr, i);
    } else if j == i + 1 {
        XorRangeExtend(arr, i, j);
        XorRangeSingle(arr, j);
    } else {
        XorRangeExtend(arr, i, j);
        XorRangeStep(arr, i+1, j);
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
    var maxXor: bv32 := arr[0];
    var i := 0;
    
    // Initialize maxXor with the first element
    assert XorRange(arr, 0, 0) == arr[0];
    
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant exists i1, j1 :: 0 <= i1 <= j1 < |arr| && i1 < i + 1 && maxXor == XorRange(arr, i1, j1)
        invariant forall i1, j1 :: 0 <= i1 <= j1 < i ==> (XorRange(arr, i1, j1) as int) <= (maxXor as int)
    {
        var currentXor: bv32 := arr[i];
        var j := i;
        
        // currentXor starts as arr[i] which equals XorRange(arr, i, i)
        XorRangeSingle(arr, i);
        assert currentXor == XorRange(arr, i, i);
        
        if (currentXor as int) > (maxXor as int) {
            maxXor := currentXor;
        }
        
        j := j + 1;
        
        while j < |arr|
            invariant i < j <= |arr|
            invariant currentXor == XorRange(arr, i, j-1)
            invariant exists i1, j1 :: 0 <= i1 <= j1 < |arr| && maxXor == XorRange(arr, i1, j1)
            invariant forall j1 :: i <= j1 < j ==> (XorRange(arr, i, j1) as int) <= (maxXor as int)
            invariant forall i1, j1 :: 0 <= i1 <= j1 < i ==> (XorRange(arr, i1, j1) as int) <= (maxXor as int)
        {
            currentXor := currentXor ^ arr[j];
            
            // Prove that currentXor == XorRange(arr, i, j)
            XorRangeStep(arr, i, j);
            assert currentXor == XorRange(arr, i, j-1) ^ arr[j];
            assert XorRange(arr, i, j) == XorRange(arr, i, j-1) ^ arr[j];
            assert currentXor == XorRange(arr, i, j);
            
            if (currentXor as int) > (maxXor as int) {
                maxXor := currentXor;
            }
            
            j := j + 1;
        }
        
        i := i + 1;
    }
    
    result := maxXor;
}
// </vc-code>

