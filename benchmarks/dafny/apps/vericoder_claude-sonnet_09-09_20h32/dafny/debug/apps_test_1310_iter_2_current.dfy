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

lemma XorRangeProperties(arr: seq<bv32>, i: int, j: int)
    requires 0 <= i <= j < |arr|
    ensures XorRange(arr, i, j) == XorRange(arr, i, j)
{
}

lemma ExistsMaxXor(arr: seq<bv32>)
    requires ValidInput(arr)
    ensures (exists i, j :: 0 <= i <= j < |arr| && 
        (forall i1, j1 :: 0 <= i1 <= j1 < |arr| ==> 
            (XorRange(arr, i1, j1) as int) <= (XorRange(arr, i, j) as int)))
{
    var n := |arr|;
    var maxVal := 0 as bv32;
    var maxI := 0;
    var maxJ := 0;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= maxI <= maxJ < n
        invariant forall i1, j1 :: 0 <= i1 < i && i1 <= j1 < n ==> 
            (XorRange(arr, i1, j1) as int) <= (XorRange(arr, maxI, maxJ) as int)
    {
        var j := i;
        while j < n
            invariant i <= j <= n
            invariant 0 <= maxI <= maxJ < n
            invariant forall i1, j1 :: 0 <= i1 < i && i1 <= j1 < n ==> 
                (XorRange(arr, i1, j1) as int) <= (XorRange(arr, maxI, maxJ) as int)
            invariant forall j1 :: i <= j1 < j ==> 
                (XorRange(arr, i, j1) as int) <= (XorRange(arr, maxI, maxJ) as int)
        {
            var currentXor := XorRange(arr, i, j);
            if (currentXor as int) > (XorRange(arr, maxI, maxJ) as int) {
                maxI := i;
                maxJ := j;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

function FindMaxXorValue(arr: seq<bv32>, currentI: int, currentJ: int, currentMax: bv32): bv32
    requires ValidInput(arr)
    requires 0 <= currentI <= currentJ < |arr|
{
    var allXors := set i, j | 0 <= i <= j < |arr| :: XorRange(arr, i, j);
    var maxXor :| maxXor in allXors && forall x :: x in allXors ==> (x as int) <= (maxXor as int);
    maxXor
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
{
    ExistsMaxXor(arr);
    
    var maxXor: bv32 := arr[0];
    var bestI: int := 0;
    var bestJ: int := 0;
    
    var i := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant 0 <= bestI <= bestJ < |arr|
        invariant maxXor == XorRange(arr, bestI, bestJ)
        invariant forall i1, j1 :: 0 <= i1 < i && i1 <= j1 < |arr| ==> 
            (XorRange(arr, i1, j1) as int) <= (maxXor as int)
    {
        var j := i;
        while j < |arr|
            invariant i <= j <= |arr|
            invariant 0 <= bestI <= bestJ < |arr|
            invariant maxXor == XorRange(arr, bestI, bestJ)
            invariant forall i1, j1 :: 0 <= i1 < i && i1 <= j1 < |arr| ==> 
                (XorRange(arr, i1, j1) as int) <= (maxXor as int)
            invariant forall j1 :: i <= j1 < j ==> 
                (XorRange(arr, i, j1) as int) <= (maxXor as int)
        {
            var currentXor := XorRange(arr, i, j);
            if (currentXor as int) > (maxXor as int) {
                maxXor := currentXor;
                bestI := i;
                bestJ := j;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := maxXor;
}
// </vc-code>

