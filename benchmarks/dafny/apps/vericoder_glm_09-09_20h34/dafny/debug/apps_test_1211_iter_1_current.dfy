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
var best_box_type := 0;
  var max_hamsters := A[0] * (n / A[0]);

  var i := 1;
  while i < k
      invariant 1 <= i <= k
      invariant 0 <= best_box_type < i
      invariant max_hamsters == A[best_box_type] * (n / A[best_box_type])
      invariant forall j :: 0 <= j < i ==> max_hamsters >= A[j] * (n / A[j])
  {
      var c := A[i];
      var transported := c * (n / c);
      if transported > max_hamsters {
          max_hamsters := transported;
          best_box_type := i;
      }
      i := i + 1;
  }

  return (best_box_type+1, n / A[best_box_type]);
// </vc-code>

