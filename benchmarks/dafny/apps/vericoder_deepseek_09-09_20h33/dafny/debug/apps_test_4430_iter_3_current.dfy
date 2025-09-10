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
lemma GreedyPackFromEndHelperDecreases(a: seq<int>, pos: int, boxes_left: int, capacity: int, current_box_space: int)
    requires capacity >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= capacity
    requires boxes_left >= 1
    requires 0 <= current_box_space <= capacity
    requires pos >= 0 && pos < |a|
    requires a[pos] <= current_box_space
    ensures GreedyPackFromEndHelper(a, pos - 1, boxes_left, capacity, current_box_space - a[pos]) < GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space)
    decreases 0
{
}

lemma GreedyPackFromEndHelperDecreases2(a: seq<int>, pos: int, boxes_left: int, capacity: int, current_box_space: int)
    requires capacity >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= capacity
    requires boxes_left >= 1
    requires 0 <= current_box_space <= capacity
    requires pos >= 0 && pos < |a|
    requires a[pos] > current_box_space && boxes_left > 1
    ensures GreedyPackFromEndHelper(a, pos - 1, boxes_left - 1, capacity, capacity - a[pos]) < GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space)
    decreases 0
{
}

lemma GreedyPackFromEndHelperZeroWhenPosNegative(a: seq<int>, pos: int, boxes_left: int, capacity: int, current_box_space: int)
    requires capacity >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= capacity
    requires boxes_left >= 1
    requires 0 <= current_box_space <= capacity
    requires pos < 0
    ensures GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 0
{
}

lemma GreedyPackFromEndHelperSameWhenPosOutOfBounds(a: seq<int>, pos: int, boxes_left: int, capacity: int, current_box_space: int)
    requires capacity >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= capacity
    requires boxes_left >= 1
    requires 0 <= current_box_space <= capacity
    requires pos >= |a|
    ensures GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 0
{
}
// </vc-helpers>
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
    result := 0;
    var pos := n - 1;
    var boxes_left := m;
    var current_box_space := k;
    
    while (pos >= 0 && boxes_left >= 1)
        invariant -1 <= pos <= n - 1
        invariant 1 <= boxes_left <= m
        invariant 0 <= current_box_space <= k
        invariant result == (n - 1 - pos) - GreedyPackFromEndHelper(a, pos, boxes_left, k, current_box_space)
        decreases pos + 1
    {
        if a[pos] <= current_box_space {
            current_box_space := current_box_space - a[pos];
            result := result + 1;
            pos := pos - 1;
        } else if boxes_left > 1 {
            boxes_left := boxes_left - 1;
            current_box_space := k - a[pos];
            result := result + 1;
            pos := pos - 1;
        } else {
            break;
        }
    }
    result := n - 1 - pos;
}
// </vc-code>

