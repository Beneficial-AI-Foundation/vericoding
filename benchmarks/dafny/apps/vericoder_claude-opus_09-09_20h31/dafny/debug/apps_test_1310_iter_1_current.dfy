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
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
{
    var maxXor: bv32 := 0;
    var i := 0;
    
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant forall i1, j1 :: 0 <= i1 <= j1 < i ==> 
            (XorRange(arr, i1, j1) as int) <= (maxXor as int)
        invariant i > 0 ==> exists i1, j1 :: 0 <= i1 <= j1 < i && 
            maxXor == XorRange(arr, i1, j1)
    {
        var currentXor: bv32 := 0;
        var j := i;
        
        while j < |arr|
            invariant i <= j <= |arr|
            invariant j > i ==> currentXor == XorRange(arr, i, j-1)
            invariant forall j1 :: i <= j1 < j ==> 
                (XorRange(arr, i, j1) as int) <= (maxXor as int)
            invariant forall i1, j1 :: 0 <= i1 <= j1 < i ==> 
                (XorRange(arr, i1, j1) as int) <= (maxXor as int)
            invariant i > 0 ==> exists i1, j1 :: 0 <= i1 <= j1 < i && 
                maxXor == XorRange(arr, i1, j1)
            invariant j == i && i == 0 ==> maxXor == 0
            invariant j > i || i > 0 ==> exists i1, j1 :: 0 <= i1 <= j1 < |arr| && 
                maxXor == XorRange(arr, i1, j1)
        {
            currentXor := currentXor ^ arr[j];
            
            if j == i {
                assert currentXor == arr[i];
                XorRangeSingle(arr, i);
                assert currentXor == XorRange(arr, i, i);
            } else {
                XorRangeExtend(arr, i, j);
                assert currentXor == XorRange(arr, i, j);
            }
            
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

