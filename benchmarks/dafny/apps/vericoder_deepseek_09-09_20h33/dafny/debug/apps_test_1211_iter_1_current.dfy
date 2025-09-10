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
lemma HamstersTransportedMonotonic(n: int, cap1: int, cap2: int)
  requires cap1 > 0 && cap2 > 0
  requires cap1 <= cap2
  ensures HamstersTransported(n, cap1) <= HamstersTransported(n, cap2)
{
}

lemma HamstersTransportedDivision(n: int, capacity: int)
  requires capacity > 0
  ensures HamstersTransported(n, capacity) == capacity * (n / capacity)
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
  var best_box := 0;
  var max_transported := -1;
  
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant best_box >= 0 && best_box <= k
    invariant max_transported >= -1
    invariant i > 0 ==> best_box >= 0 && best_box < k
    invariant i > 0 ==> max_transported == HamstersTransported(n, A[best_box])
    invariant forall j :: 0 <= j < i ==> HamstersTransported(n, A[j]) <= max_transported
  {
    var transported := HamstersTransported(n, A[i]);
    if transported > max_transported || max_transported == -1 {
      best_box := i;
      max_transported := transported;
    }
    i := i + 1;
  }
  
  box_type := best_box + 1;
  num_boxes := n / A[best_box];
}
// </vc-code>

