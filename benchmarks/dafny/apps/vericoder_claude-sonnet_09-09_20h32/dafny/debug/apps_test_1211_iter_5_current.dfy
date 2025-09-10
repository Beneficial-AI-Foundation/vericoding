predicate ValidInput(n: int, k: int, A: seq<int>)
{
    k > 0 && |A| == k && (forall i :: 0 <= i < k ==> A[i] > 0) && n >= 0
}

function HamstersTransported(n: int, capacity: int): int
    requires capacity > 0
{
    capacity * (n / capacity)
}

predicate OptimalSolution(n: int, A: seq<int>, box_type: int, num_boxes: int)
    requires ValidInput(n, |A|, A)
    requires 1 <= box_type <= |A|
{
    num_boxes == n / A[box_type - 1] &&
    forall i :: 0 <= i < |A| ==> HamstersTransported(n, A[box_type - 1]) >= HamstersTransported(n, A[i])
}

// <vc-helpers>
lemma OptimalBoxTypeExists(n: int, A: seq<int>)
    requires ValidInput(n, k, A)
    ensures exists i :: 1 <= i <= |A| && 
            (forall j :: 0 <= j < |A| ==> HamstersTransported(n, A[i-1]) >= HamstersTransported(n, A[j]))
{
    var maxTransported := HamstersTransported(n, A[0]);
    var maxIndex := 0;
    
    assert forall i :: 0 <= i < |A| ==> HamstersTransported(n, A[i]) <= n;
    
    var i := 1;
    while i < |A|
        invariant 1 <= i <= |A|
        invariant 0 <= maxIndex < i
        invariant maxTransported == HamstersTransported(n, A[maxIndex])
        invariant forall j :: 0 <= j < i ==> HamstersTransported(n, A[maxIndex]) >= HamstersTransported(n, A[j])
    {
        if HamstersTransported(n, A[i]) > maxTransported {
            maxTransported := HamstersTransported(n, A[i]);
            maxIndex := i;
        }
        i := i + 1;
    }
    
    assert forall j :: 0 <= j < |A| ==> HamstersTransported(n, A[maxIndex]) >= HamstersTransported(n, A[j]);
    assert 1 <= maxIndex + 1 <= |A|;
    assert forall j :: 0 <= j < |A| ==> HamstersTransported(n, A[maxIndex]) >= HamstersTransported(n, A[j]);
}

lemma DivisionProperty(n: int, cap1: int, cap2: int)
    requires cap1 > 0 && cap2 > 0
    requires cap1 * (n / cap1) >= cap2 * (n / cap2)
    ensures cap1 * (n / cap1) >= cap2 * (n / cap2)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, A: seq<int>) returns (box_type: int, num_boxes: int)
    requires ValidInput(n, k, A)
    ensures 1 <= box_type <= k
    ensures num_boxes >= 0
    ensures OptimalSolution(n, A, box_type, num_boxes)
// </vc-spec>
// <vc-code>
{
    box_type := 1;
    num_boxes := n / A[0];
    var max_transported := HamstersTransported(n, A[0]);
    
    var i := 1;
    while i < k
        invariant 1 <= i <= k
        invariant 1 <= box_type <= k
        invariant max_transported == HamstersTransported(n, A[box_type - 1])
        invariant num_boxes == n / A[box_type - 1]
        invariant forall j :: 0 <= j < i ==> HamstersTransported(n, A[box_type - 1]) >= HamstersTransported(n, A[j])
    {
        var current_transported := HamstersTransported(n, A[i]);
        if current_transported > max_transported {
            box_type := i + 1;
            num_boxes := n / A[i];
            max_transported := current_transported;
        }
        i := i + 1;
    }
    
    assert forall j :: 0 <= j < k ==> HamstersTransported(n, A[box_type - 1]) >= HamstersTransported(n, A[j]);
    assert k == |A|;
    assert forall j :: 0 <= j < |A| ==> HamstersTransported(n, A[box_type - 1]) >= HamstersTransported(n, A[j]);
}
// </vc-code>

