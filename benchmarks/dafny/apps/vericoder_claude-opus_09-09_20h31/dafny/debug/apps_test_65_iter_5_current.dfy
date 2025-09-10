function seq_min(s: seq<int>): int
    requires |s| > 0
    ensures seq_min(s) in s
    ensures forall k :: 0 <= k < |s| ==> seq_min(s) <= s[k]
{
    if |s| == 1 then s[0]
    else if s[0] <= seq_min(s[1..]) then s[0]
    else seq_min(s[1..])
}

predicate ValidInput(arr: seq<int>)
{
    |arr| >= 2 && 
    exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr)
}

// <vc-helpers>
lemma MinElementProperties(arr: seq<int>, minVal: int, i: int)
    requires |arr| > 0
    requires minVal == seq_min(arr)
    requires 0 <= i < |arr|
    ensures arr[i] >= minVal
{
    // This follows directly from the postcondition of seq_min
}

lemma MinInTail(arr: seq<int>, i: int)
    requires |arr| > 1
    requires 0 < i < |arr|
    requires arr[i] == seq_min(arr)
    ensures arr[i] == seq_min(arr[1..])
{
    assert arr[i] in arr[1..];
    assert forall k :: 0 <= k < |arr[1..]| ==> seq_min(arr[1..]) <= arr[1..][k];
    assert forall k :: 1 <= k < |arr| ==> arr[i] <= arr[k];
}

lemma ValidInputImpliesMinDistance(arr: seq<int>)
    requires ValidInput(arr)
    ensures exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) && j - i <= |arr| - 1
{
    var i, j :| 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr);
    assert j - i <= |arr| - 1;
}

lemma ValidInputGuaranteesPair(arr: seq<int>)
    requires ValidInput(arr)
    ensures exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr)
{
    // This follows directly from ValidInput
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result > 0
    ensures result <= |arr| - 1
    ensures exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) && j - i == result
    ensures forall i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) ==> j - i >= result
// </vc-spec>
// <vc-code>
{
    var minVal := seq_min(arr);
    var firstPos := -1;
    var minDistance := |arr|;
    var foundPair := false;
    
    var i := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant minVal == seq_min(arr)
        invariant firstPos == -1 || (0 <= firstPos < i && firstPos < |arr| && arr[firstPos] == minVal)
        invariant minDistance > 0
        invariant minDistance <= |arr|
        invariant foundPair ==> minDistance < |arr|
        invariant foundPair ==> exists p, q :: 0 <= p < q < |arr| && q <= i && arr[p] == arr[q] == minVal && q - p == minDistance
        invariant foundPair ==> forall p, q :: 0 <= p < q < |arr| && q <= i && arr[p] == arr[q] == minVal ==> q - p >= minDistance
        invariant !foundPair ==> forall p, q :: 0 <= p < q < i && arr[p] == minVal && arr[q] == minVal ==> false
        invariant firstPos != -1 && !foundPair ==> exists j :: i <= j < |arr| && arr[j] == minVal
        invariant forall p, q :: 0 <= p < q < |arr| && arr[p] == arr[q] == minVal && q <= i ==> foundPair
    {
        if arr[i] == minVal {
            if firstPos == -1 {
                firstPos := i;
            } else {
                var dist := i - firstPos;
                if dist < minDistance {
                    minDistance := dist;
                }
                foundPair := true;
                firstPos := i;
            }
        }
        i := i + 1;
    }
    
    assert foundPair by {
        ValidInputGuaranteesPair(arr);
    }
    
    assert exists p, q :: 0 <= p < q < |arr| && arr[p] == arr[q] == minVal && q - p == minDistance;
    assert forall p, q :: 0 <= p < q < |arr| && arr[p] == arr[q] == minVal ==> q - p >= minDistance;
    
    result := minDistance;
}
// </vc-code>

