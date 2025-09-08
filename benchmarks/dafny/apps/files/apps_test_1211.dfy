Given N hamsters and K types of boxes with capacities, find which single box type
to buy (and how many boxes) to transport the maximum number of hamsters.
Each box must be completely filled.

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

method solve(n: int, k: int, A: seq<int>) returns (box_type: int, num_boxes: int)
    requires ValidInput(n, k, A)
    ensures 1 <= box_type <= k
    ensures num_boxes >= 0
    ensures OptimalSolution(n, A, box_type, num_boxes)
{
    var mx := 0;
    var mxval := A[0] * (n / A[0]);

    for i := 1 to k
        invariant 0 <= mx < k
        invariant mxval >= 0
        invariant mxval == A[mx] * (n / A[mx])
        invariant forall j :: 0 <= j < i ==> A[mx] * (n / A[mx]) >= A[j] * (n / A[j])
        invariant forall j :: 0 <= j < mx ==> A[j] * (n / A[j]) < A[mx] * (n / A[mx])
    {
        var boxes_of_type_i := n / A[i];
        var hamsters_transported := A[i] * boxes_of_type_i;

        if hamsters_transported > mxval {
            mxval := hamsters_transported;
            mx := i;
        }
    }

    box_type := mx + 1;
    num_boxes := n / A[mx];
}
