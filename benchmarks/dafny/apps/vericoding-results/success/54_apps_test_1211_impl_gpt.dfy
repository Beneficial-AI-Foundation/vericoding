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
  var i := 0;
  var best := 0;
  while i < k
    invariant 0 <= i <= k
    invariant 0 <= best < k
    invariant A[best] > 0
    invariant forall j :: 0 <= j < i ==> A[j] > 0
    invariant forall j :: 0 <= j < i ==> HamstersTransported(n, A[best]) >= HamstersTransported(n, A[j])
    decreases k - i
  {
    assert 0 <= i && i < k;
    assert A[i] > 0;
    if HamstersTransported(n, A[i]) >= HamstersTransported(n, A[best]) {
      best := i;
    }
    i := i + 1;
  }
  box_type := best + 1;
  num_boxes := n / A[best];
}
// </vc-code>

