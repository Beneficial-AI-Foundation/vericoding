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
lemma GreedyPackFromEndHelperBounds(a: seq<int>, pos: int, boxes_left: int, capacity: int, current_box_space: int)
    requires capacity >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= capacity
    requires boxes_left >= 1
    requires 0 <= current_box_space <= capacity
    ensures 0 <= GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) <= (if pos >= 0 then pos + 1 else 0)
    ensures GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) <= |a|
    decreases if pos >= 0 then pos + 1 else 0
{
    if pos < 0 {
        assert GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 0;
    } else if pos >= |a| {
        assert GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 0;
    } else if a[pos] > capacity {
        assert GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 0;
    } else if a[pos] <= current_box_space {
        GreedyPackFromEndHelperBounds(a, pos - 1, boxes_left, capacity, current_box_space - a[pos]);
        assert GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 
               1 + GreedyPackFromEndHelper(a, pos - 1, boxes_left, capacity, current_box_space - a[pos]);
    } else if boxes_left > 1 {
        GreedyPackFromEndHelperBounds(a, pos - 1, boxes_left - 1, capacity, capacity - a[pos]);
        assert GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 
               1 + GreedyPackFromEndHelper(a, pos - 1, boxes_left - 1, capacity, capacity - a[pos]);
    } else {
        assert GreedyPackFromEndHelper(a, pos, boxes_left, capacity, current_box_space) == 0;
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
        return 0;
    }
    
    // Apply the bounds lemma to establish that the result is bounded by n
    GreedyPackFromEndHelperBounds(a, n - 1, m, k, k);
    assert GreedyPackFromEndHelper(a, n - 1, m, k, k) <= n;
    
    var packed := 0;
    var pos := n - 1;
    var boxes_left := m;
    var current_box_space := k;
    
    while pos >= 0 && boxes_left > 0
        invariant -1 <= pos < n
        invariant 0 <= boxes_left <= m
        invariant 0 <= current_box_space <= k
        invariant packed >= 0
        invariant boxes_left > 0 ==> packed + GreedyPackFromEndHelper(a, pos, boxes_left, k, current_box_space) == GreedyPackFromEndHelper(a, n - 1, m, k, k)
        invariant boxes_left == 0 ==> packed == GreedyPackFromEndHelper(a, n - 1, m, k, k)
        invariant packed <= n
    {
        if a[pos] <= current_box_space {
            packed := packed + 1;
            current_box_space := current_box_space - a[pos];
        } else if boxes_left > 1 {
            packed := packed + 1;
            boxes_left := boxes_left - 1;
            current_box_space := k - a[pos];
        } else {
            // Current item doesn't fit and no more boxes available
            // boxes_left == 1 here, so we're out of boxes
            break;
        }
        pos := pos - 1;
    }
    
    assert packed == GreedyPackFromEndHelper(a, n - 1, m, k, k);
    assert GreedyPackFromEnd(a, m, k) == GreedyPackFromEndHelper(a, |a| - 1, m, k, k);
    assert |a| == n;
    
    return packed;
}
// </vc-code>

