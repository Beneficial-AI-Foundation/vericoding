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
  var max_trans := HamstersTransported(n, A[0]);
  var best_i := 0;
  var i := 1;
  while i < k
    invariant 0 <= i <= k
    invariant 0 <= best_i < k
    invariant max_trans >= 0
    invariant max_trans == HamstersTransported(n, A[best_i])
    invariant forall j :: 0 <= j < i ==> HamstersTransported(n, A[best_i]) >= HamstersTransported(n, A[j])
  {
    var current_trans := HamstersTransported(n, A[i]);
    if current_trans > max_trans {
      max_trans := current_trans;
      best_i := i;
    }
    i := i + 1;
  }
  box_type := best_i + 1;
  num_boxes := n / A[best_i];
}
// </vc-code>

