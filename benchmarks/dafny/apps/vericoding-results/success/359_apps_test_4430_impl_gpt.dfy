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
lemma GreedyPackFromEndHelper_Bounds(a: seq<int>, pos: int, boxes_left: int, capacity: int, current_box_space: int)
    requires capacity >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= capacity
    requires boxes_left >= 1
    requires 0 <= current_box_space <= capacity
    requires -1 <= pos < |a|
    ensures 0 <= GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) <= pos + 1
    decreases pos + 1
{
    reveal GreedyPackFromEndHelper();
    if pos < 0 {
        assert GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 0;
    } else {
        assert pos < |a|;
        assert 1 <= a[pos];
        assert a[pos] <= capacity;
        if a[pos] <= current_box_space {
            assert 0 <= current_box_space - a[pos] <= capacity;
            var t := GreedyPackFromEndHelper(a, pos - 1, boxes_left, capacity, current_box_space - a[pos]);
            GreedyPackFromEndHelper_Bounds(a, pos - 1, boxes_left, capacity, current_box_space - a[pos]);
            assert 0 <= t <= pos;
            assert GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 1 + t;
            assert 0 <= 1 + t <= pos + 1;
        } else {
            if boxes_left > 1 {
                assert 0 <= capacity - a[pos] <= capacity;
                var t := GreedyPackFromEndHelper(a, pos - 1, boxes_left - 1, capacity, capacity - a[pos]);
                GreedyPackFromEndHelper_Bounds(a, pos - 1, boxes_left - 1, capacity, capacity - a[pos]);
                assert 0 <= t <= pos;
                assert GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 1 + t;
                assert 0 <= 1 + t <= pos + 1;
            } else {
                assert GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 0;
            }
        }
    }
}

lemma GreedyPackFromEnd_Bounds(a: seq<int>, boxes: int, capacity: int)
    requires boxes >= 1
    requires capacity >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= capacity
    ensures 0 <= GreedyPackFromEnd(a, boxes, capacity) <= |a|
{
    reveal GreedyPackFromEnd();
    assert -1 <= |a| - 1 < |a|;
    GreedyPackFromEndHelper_Bounds(a, |a| - 1, boxes, capacity, capacity);
}
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
  GreedyPackFromEnd_Bounds(a, m, k);
  result := GreedyPackFromEnd(a, m, k);
}
// </vc-code>

