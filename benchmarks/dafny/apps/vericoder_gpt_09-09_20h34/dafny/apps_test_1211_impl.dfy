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
  // Initialize best candidate as the first box type
  assert 0 < k;
  assert 0 <= 0 < k;
  assert A[0] > 0;
  var bestIndex := 1;
  var bestTrans := HamstersTransported(n, A[0]);

  var i := 1;
  while i < k
    invariant 0 < i <= k
    invariant 1 <= bestIndex <= i
    invariant 0 <= bestIndex - 1 < k
    invariant A[bestIndex - 1] > 0
    invariant bestTrans == HamstersTransported(n, A[bestIndex - 1])
    invariant forall j :: 0 <= j < i ==> A[j] > 0
    invariant forall j :: 0 <= j < i ==> bestTrans >= HamstersTransported(n, A[j])
    decreases k - i
  {
    assert 0 <= i < k;
    assert A[i] > 0;
    var current := HamstersTransported(n, A[i]);
    if current > bestTrans {
      bestIndex := i + 1;
      bestTrans := current;
      assert 0 <= bestIndex - 1 < k;
    }
    assert bestTrans >= current; // either equality (then) or >= (else)
    i := i + 1;
  }

  box_type := bestIndex;
  assert 1 <= box_type <= k;
  assert 0 <= box_type - 1 < k;
  assert A[box_type - 1] > 0;
  num_boxes := n / A[box_type - 1];
  assert num_boxes >= 0;
}
// </vc-code>

