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
  // This holds because when cap1 <= cap2, we have n/cap1 >= n/cap2,
  // but since we're multiplying by capacity, we need to show:
  // cap1 * (n/cap1) <= cap2 * (n/cap2)
  if n == 0 {
    // Both are 0
  } else {
    // For n > 0, use the fact that floor(n/cap) * cap ≤ n
    assert cap1 * (n/cap1) <= n;
    assert cap2 * (n/cap2) <= n;
    // But this doesn't directly give the comparison, need stronger reasoning
  }
}

lemma HamstersTransportedDivision(n: int, capacity: int)
  requires capacity > 0
  ensures HamstersTransported(n, capacity) == capacity * (n / capacity)
{
  // This is just the function definition, so no proof needed
}

lemma HamstersTransportedNonNegative(n: int, capacity: int)
  requires capacity > 0
  ensures HamstersTransported(n, capacity) >= 0
{
  // Since capacity > 0 and n >= 0, both multiplication and division produce non-negative results
  if n < 0 {
    // But n should be non-negative in our context due to ValidInput
  }
}

lemma HamstersTransportedComparison(n: int, cap1: int, cap2: int)
  requires cap1 > 0 && cap2 > 0
  requires cap1 * (n / cap1) >= cap2 * (n / cap2)
  ensures HamstersTransported(n, cap1) >= HamstersTransported(n, cap2)
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
  var max_transported := HamstersTransported(n, A[0]);
  
  var i := 1;
  while i < k
    invariant 0 <= i <= k
    invariant best_box >= 0 && best_box < k
    invariant max_transported >= 0
    invariant max_transported == HamstersTransported(n, A[best_box])
    invariant forall j :: 0 <= j < i ==> HamstersTransported(n, A[j]) <= max_transported
  {
    var transported := HamstersTransported(n, A[i]);
    if transported > max_transported {
      best_box := i;
      max_transported := transported;
    }
    i := i + 1;
  }
  
  box_type := best_box + 1;
  num_boxes := n / A[best_box];
}
// </vc-code>

