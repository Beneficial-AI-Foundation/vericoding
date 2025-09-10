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
// No additional helpers required.
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
  var best := 0;
  var bestTransport := HamstersTransported(n, A[0]);
  var idx := 1;
  while idx < k
    invariant 1 <= k
    invariant 0 <= best < idx <= k
    invariant bestTransport == HamstersTransported(n, A[best])
    invariant forall j :: 0 <= j < idx ==> bestTransport >= HamstersTransported(n, A[j])
  {
    var cur := HamstersTransported(n, A[idx]);
    if cur > bestTransport {
      bestTransport := cur;
      best := idx;
    }
    idx := idx + 1;
  }
  box_type := best + 1;
  num_boxes := n / A[best];
}
// </vc-code>

