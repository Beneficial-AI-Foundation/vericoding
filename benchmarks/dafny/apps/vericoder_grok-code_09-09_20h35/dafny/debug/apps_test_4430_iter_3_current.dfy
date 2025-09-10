function GreedyPackFromEnd(a: seq<int>, boxes: int, capacity: int): int
    requires boxes >= 1
    requires capacity >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= capacity
{
    GreedyPackFromEndHelper(a, |a| - 1, boxes, capacity, capacity)
}

function GreedyPackFromEndHelper(a: seq<int>, pos: int, boxes_left: int, capacity: int, current_box_space: int): int
    requires capacity >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= capacity
    requires boxes_left >= 1
    requires 0 <= current_box_space <= capacity
    decreases pos + 1
{
    if pos < 0 then 0
    else if pos >= |a| then 0
    else if a[pos] > capacity then 0
    else if a[pos] <= current_box_space then
        1 + GreedyPackFromEndHelper(a, pos - 1, boxes_left, capacity, current_box_space - a[pos])
    else if boxes_left > 1 then
        1 + GreedyPackFromEndHelper(a, pos - 1, boxes_left - 1, capacity, capacity - a[pos])
    else
        0
}

// <vc-helpers>
// No additional helpers needed as the iterative implementation uses the provided function definitions for verification via invariants and postcondition.
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int, a: seq<int>) returns (result: int)
    requires n >= 0
    requires m >= 1
    requires k >= 1
    requires |a| == n
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= k
    ensures 0 <= result <= n
    ensures result == GreedyPackFromEnd(a, m, k)
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var pos := n - 1;
  var boxes_left := m;
  var current_box_space := k;

  while pos >= 0
    invariant -1 <= pos <= n - 1
    invariant count + GreedyPackFromEndHelper(a, pos, boxes_left, k, current_box_space) == GreedyPackFromEnd(a, m, k)
    invariant boxes_left >= 1 && boxes_left <= m
    invariant 0 <= current_box_space <= k
    invariant 0 <= count <= n - pos - 1
    decreases pos
  {
    if a[pos] <= current_box_space {
      count := count + 1;
      current_box_space := current_box_space - a[pos];
    } else if boxes_left > 1 {
      count := count + 1;
      boxes_left := boxes_left - 1;
      current_box_space := k - a[pos];
    } else {
      // Cannot pack this item, skip
    }
    pos := pos - 1;
  }

  result := count;
}
// </vc-code>

