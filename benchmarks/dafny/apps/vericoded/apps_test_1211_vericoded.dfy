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
lemma MaxExists(n: int, A: seq<int>)
    requires ValidInput(n, |A|, A)
    ensures exists i :: 0 <= i < |A| && (forall j :: 0 <= j < |A| ==> HamstersTransported(n, A[i]) >= HamstersTransported(n, A[j]))
{
    // The maximum exists because A is non-empty (k > 0) and finite
    var max_idx := 0;
    var idx := 1;
    while idx < |A|
        invariant 0 <= max_idx < idx <= |A|
        invariant forall j :: 0 <= j < idx ==> HamstersTransported(n, A[max_idx]) >= HamstersTransported(n, A[j])
    {
        if HamstersTransported(n, A[idx]) > HamstersTransported(n, A[max_idx]) {
            max_idx := idx;
        }
        idx := idx + 1;
    }
    assert forall j :: 0 <= j < |A| ==> HamstersTransported(n, A[max_idx]) >= HamstersTransported(n, A[j]);
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
    var max_transported := HamstersTransported(n, A[0]);
    var best_idx := 0;
    
    var i := 1;
    while i < k
        invariant 0 <= best_idx < i <= k
        invariant max_transported == HamstersTransported(n, A[best_idx])
        invariant forall j :: 0 <= j < i ==> HamstersTransported(n, A[best_idx]) >= HamstersTransported(n, A[j])
    {
        var curr_transported := HamstersTransported(n, A[i]);
        if curr_transported > max_transported {
            max_transported := curr_transported;
            best_idx := i;
        }
        i := i + 1;
    }
    
    assert i == k;
    assert forall j :: 0 <= j < k ==> HamstersTransported(n, A[best_idx]) >= HamstersTransported(n, A[j]);
    assert forall j :: 0 <= j < |A| ==> HamstersTransported(n, A[best_idx]) >= HamstersTransported(n, A[j]);
    
    box_type := best_idx + 1;
    num_boxes := n / A[best_idx];
}
// </vc-code>

