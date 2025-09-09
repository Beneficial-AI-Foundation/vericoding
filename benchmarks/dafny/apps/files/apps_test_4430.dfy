Given n objects with sizes and m boxes of capacity k, find the maximum number of objects
that can be packed using a greedy algorithm by potentially removing leftmost objects.
The greedy algorithm processes objects from left to right, placing each object in the
current box if it fits, otherwise using a new empty box.

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

method solve(n: int, m: int, k: int, a: seq<int>) returns (result: int)
    requires n >= 0
    requires m >= 1
    requires k >= 1
    requires |a| == n
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= k
    ensures 0 <= result <= n
    ensures result == GreedyPackFromEnd(a, m, k)
{
    var b := k;
    var count := 0;
    var boxes_left := m;

    var i := n - 1;
    while i >= 0
        invariant -1 <= i <= n - 1
        invariant 0 <= count <= n - 1 - i
        invariant boxes_left >= 1
        invariant 0 <= b <= k
        invariant count == GreedyPackFromEnd(a, m, k) - GreedyPackFromEndHelper(a, i, boxes_left, k, b)
    {
        var obj := a[i];
        if obj > k {
            break;
        }
        if obj > b {
            if boxes_left > 1 {
                boxes_left := boxes_left - 1;
                b := k - obj;
                count := count + 1;
            } else {
                break;
            }
        } else {
            b := b - obj;
            count := count + 1;
        }
        i := i - 1;
    }

    result := count;
}
