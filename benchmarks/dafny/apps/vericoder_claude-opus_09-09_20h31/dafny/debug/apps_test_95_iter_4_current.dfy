predicate ValidInput(n: nat, arr: seq<int>)
{
    n > 0 && |arr| == n && forall i :: 0 <= i < |arr| ==> arr[i] >= 1
}

predicate IsUnimodal(arr: seq<int>)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
{
    if |arr| <= 1 then true
    else
        var phases := ComputePhases(arr);
        phases.0 <= phases.1 <= phases.2 == |arr| &&
        (forall i, j :: 0 <= i < j < phases.0 ==> arr[i] < arr[j]) &&
        (forall i :: phases.0 <= i < phases.1 ==> arr[i] == (if phases.0 > 0 then arr[phases.0] else arr[0])) &&
        (forall i, j :: phases.1 <= i < j < phases.2 ==> arr[i] > arr[j]) &&
        (phases.0 > 0 && phases.1 < |arr| ==> arr[phases.0-1] >= (if phases.1 > phases.0 then arr[phases.0] else arr[phases.1]))
}

function ComputePhases(arr: seq<int>): (int, int, int)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    ensures var (incEnd, constEnd, decEnd) := ComputePhases(arr); 0 <= incEnd <= constEnd <= decEnd <= |arr|
{
    var incEnd := ComputeIncreasingEnd(arr, 0, 0);
    var constEnd := ComputeConstantEnd(arr, incEnd, if incEnd > 0 then arr[incEnd-1] else 0);
    var decEnd := ComputeDecreasingEnd(arr, constEnd, if constEnd > incEnd then arr[incEnd] else if incEnd > 0 then arr[incEnd-1] else 0);
    (incEnd, constEnd, decEnd)
}

// <vc-helpers>
function ComputeIncreasingEnd(arr: seq<int>, start: int, prevVal: int): int
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    requires 0 <= start <= |arr|
    requires prevVal >= 0
    requires start > 0 ==> prevVal == arr[start-1]
    requires forall i, j :: 0 <= i < j < start ==> arr[i] < arr[j]
    ensures 0 <= ComputeIncreasingEnd(arr, start, prevVal) <= |arr|
    ensures var end := ComputeIncreasingEnd(arr, start, prevVal);
            forall i, j :: 0 <= i < j < end ==> arr[i] < arr[j]
    ensures var end := ComputeIncreasingEnd(arr, start, prevVal);
            end < |arr| && end > 0 ==> arr[end-1] >= arr[end]
    decreases |arr| - start
{
    if start >= |arr| then start
    else if start == 0 || arr[start] > prevVal then
        ComputeIncreasingEnd(arr, start + 1, arr[start])
    else start
}

function ComputeConstantEnd(arr: seq<int>, start: int, val: int): int
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    requires 0 <= start <= |arr|
    requires val >= 0
    requires start > 0 ==> val == arr[start-1]
    ensures start <= ComputeConstantEnd(arr, start, val) <= |arr|
    ensures var end := ComputeConstantEnd(arr, start, val);
            forall i :: start <= i < end && start < |arr| ==> arr[i] == arr[start]
    ensures var end := ComputeConstantEnd(arr, start, val);
            end < |arr| && start < end ==> arr[end] != arr[start]
    decreases |arr| - start
{
    if start >= |arr| then start
    else if val == 0 || arr[start] == val then
        ComputeConstantEnd(arr, start + 1, arr[start])
    else start
}

function ComputeDecreasingEnd(arr: seq<int>, start: int, prevVal: int): int
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    requires 0 <= start <= |arr|
    requires prevVal >= 0
    requires start > 0 ==> prevVal == arr[start-1]
    ensures start <= ComputeDecreasingEnd(arr, start, prevVal) <= |arr|
    ensures var end := ComputeDecreasingEnd(arr, start, prevVal);
            forall i, j :: start <= i < j < end ==> arr[i] > arr[j]
    ensures var end := ComputeDecreasingEnd(arr, start, prevVal);
            end < |arr| && start < end ==> arr[end-1] <= arr[end]
    decreases |arr| - start
{
    if start >= |arr| then start
    else if prevVal == 0 || arr[start] < prevVal then
        ComputeDecreasingEnd(arr, start + 1, arr[start])
    else start
}

lemma ComputePhasesCorrect(arr: seq<int>)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    ensures var (incEnd, constEnd, decEnd) := ComputePhases(arr);
            incEnd <= constEnd <= decEnd <= |arr| &&
            (forall i, j :: 0 <= i < j < incEnd ==> arr[i] < arr[j]) &&
            (forall i :: incEnd <= i < constEnd && incEnd < |arr| ==> arr[i] == arr[incEnd]) &&
            (forall i, j :: constEnd <= i < j < decEnd ==> arr[i] > arr[j]) &&
            (decEnd == |arr| ==> IsUnimodal(arr))
{
}

lemma UnimodalImpliesFullDecreasing(arr: seq<int>)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    requires IsUnimodal(arr)
    ensures var phases := ComputePhases(arr); phases.2 == |arr|
{
    if |arr| <= 1 {
        var phases := ComputePhases(arr);
        assert phases == (ComputeIncreasingEnd(arr, 0, 0), 
                         ComputeConstantEnd(arr, ComputeIncreasingEnd(arr, 0, 0), if ComputeIncreasingEnd(arr, 0, 0) > 0 then arr[ComputeIncreasingEnd(arr, 0, 0)-1] else 0),
                         ComputeDecreasingEnd(arr, ComputeConstantEnd(arr, ComputeIncreasingEnd(arr, 0, 0), if ComputeIncreasingEnd(arr, 0, 0) > 0 then arr[ComputeIncreasingEnd(arr, 0, 0)-1] else 0), 
                                            if ComputeConstantEnd(arr, ComputeIncreasingEnd(arr, 0, 0), if ComputeIncreasingEnd(arr, 0, 0) > 0 then arr[ComputeIncreasingEnd(arr, 0, 0)-1] else 0) > ComputeIncreasingEnd(arr, 0, 0) then arr[ComputeIncreasingEnd(arr, 0, 0)] else if ComputeIncreasingEnd(arr, 0, 0) > 0 then arr[ComputeIncreasingEnd(arr, 0, 0)-1] else 0));
    }
}

method CheckUnimodal(n: nat, arr: seq<int>) returns (isUnimodal: bool)
    requires ValidInput(n, arr)
    ensures isUnimodal <==> IsUnimodal(arr)
{
    if n <= 1 {
        return true;
    }
    
    var i := 0;
    
    // Find end of increasing phase
    while i < n - 1 && arr[i] < arr[i + 1]
        invariant 0 <= i < n
        invariant forall j, k :: 0 <= j < k <= i ==> arr[j] < arr[k]
        invariant i > 0 ==> arr[i-1] < arr[i]
    {
        i := i + 1;
    }
    var incEnd := i + 1;
    
    // Find end of constant phase  
    while i < n - 1 && arr[i] == arr[i + 1]
        invariant 0 <= i < n
        invariant incEnd - 1 <= i < n
        invariant forall j :: incEnd - 1 <= j <= i ==> arr[j] == arr[incEnd - 1]
    {
        i := i + 1;
    }
    var constEnd := i + 1;
    
    // Find end of decreasing phase
    while i < n - 1 && arr[i] > arr[i + 1]
        invariant 0 <= i < n
        invariant constEnd - 1 <= i < n
        invariant forall j, k :: constEnd - 1 <= j < k <= i ==> arr[j] > arr[k]
        invariant i > constEnd - 1 ==> arr[i-1] > arr[i]
    {
        i := i + 1;
    }
    
    // Check if we've reached the end
    isUnimodal := (i == n - 1);
    
    // Prove the postcondition
    var phases := ComputePhases(arr);
    assert phases.0 <= phases.1 <= phases.2 <= |arr|;
    
    if isUnimodal {
        assert incEnd <= constEnd <= n;
        assert forall j, k :: 0 <= j < k < incEnd ==> arr[j] < arr[k];
        
        // The key insight: if we've successfully traversed all phases and reached the end,
        // then the array satisfies the unimodal property
        assert i == n - 1;
        
        // This means we have a valid increasing-constant-decreasing sequence that covers the whole array
        if phases.2 < |arr| {
            // If phases.2 < |arr|, then by definition of IsUnimodal, the array cannot be unimodal
            // But we know it is unimodal from our traversal
            assert IsUnimodal(arr);
            UnimodalImpliesFullDecreasing(arr);
            assert phases.2 == |arr|;
        }
        assert IsUnimodal(arr);
    } else {
        if IsUnimodal(arr) {
            UnimodalImpliesFullDecreasing(arr);
            assert phases.2 == |arr|;
            assert false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, arr: seq<int>) returns (result: string)
    requires ValidInput(n, arr)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> IsUnimodal(arr)
// </vc-spec>
// <vc-code>
{
    var isUnimodal := CheckUnimodal(n, arr);
    if isUnimodal {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

