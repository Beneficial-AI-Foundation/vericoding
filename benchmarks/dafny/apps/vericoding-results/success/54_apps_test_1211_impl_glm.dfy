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
    var max_transport := HamstersTransported(n, A[0]);
    var box_type_candidate := 1;
    for i := 1 to |A|
        invariant 1 <= box_type_candidate <= k
        invariant forall j :: 0 <= j < i ==> HamstersTransported(n, A[j]) <= max_transport
        invariant 0 <= box_type_candidate-1 < |A| && HamstersTransported(n, A[box_type_candidate-1]) == max_transport
    {
        var t := HamstersTransported(n, A[i]);
        if t > max_transport
        {
            max_transport := t;
            box_type_candidate := i+1;
        }
    }
    box_type := box_type_candidate;
    num_boxes := n / A[box_type_candidate-1];
}
// </vc-code>

