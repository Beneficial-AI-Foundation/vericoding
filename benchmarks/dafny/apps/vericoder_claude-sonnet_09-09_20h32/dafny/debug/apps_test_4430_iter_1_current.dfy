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
method GreedyPackFromEndImperative(a: seq<int>, boxes: int, capacity: int) returns (result: int)
    requires boxes >= 1
    requires capacity >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= capacity
    ensures result == GreedyPackFromEnd(a, boxes, capacity)
    ensures 0 <= result <= |a|
{
    if |a| == 0 {
        return 0;
    }
    
    var pos := |a| - 1;
    var boxes_left := boxes;
    var current_box_space := capacity;
    result := 0;
    
    while pos >= 0
        invariant -1 <= pos < |a|
        invariant boxes_left >= 1
        invariant 0 <= current_box_space <= capacity
        invariant 0 <= result <= |a| - pos - 1
        invariant result + GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == GreedyPackFromEnd(a, boxes, capacity)
        decreases pos + 1
    {
        if a[pos] <= current_box_space {
            result := result + 1;
            current_box_space := current_box_space - a[pos];
        } else if boxes_left > 1 {
            result := result + 1;
            boxes_left := boxes_left - 1;
            current_box_space := capacity - a[pos];
        } else {
            break;
        }
        pos := pos - 1;
    }
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
    if n == 0 {
        result := 0;
        return;
    }
    
    result := GreedyPackFromEndImperative(a, m, k);
}
// </vc-code>

