Given a staircase with n stairs at non-decreasing heights, process m boxes thrown sequentially.
Each box has width w and height h, covering stairs 1 through w. A box falls until its bottom 
touches either a stair top or a previously placed box top within its coverage area.
Determine the landing height of each box's bottom.

function max(a: int, b: int): int
{
    if a >= b then a else b
}

predicate ValidStairs(stair_heights: seq<int>)
{
    |stair_heights| >= 1 &&
    (forall i :: 0 <= i < |stair_heights| - 1 ==> stair_heights[i] <= stair_heights[i + 1]) &&
    (forall i :: 0 <= i < |stair_heights| ==> stair_heights[i] >= 0)
}

predicate ValidBoxes(boxes: seq<(int, int)>, stairs_amount: int)
{
    forall i :: 0 <= i < |boxes| ==> boxes[i].0 >= 1 && boxes[i].0 <= stairs_amount && boxes[i].1 >= 1
}

predicate ValidResult(result: seq<int>, boxes: seq<(int, int)>, stair_heights: seq<int>)
    requires |stair_heights| >= 1
    requires forall i :: 0 <= i < |boxes| ==> boxes[i].0 >= 1 && boxes[i].0 <= |stair_heights|
{
    |result| == |boxes| &&
    (forall i :: 0 <= i < |boxes| ==> result[i] >= 0) &&
    (forall i :: 0 <= i < |boxes| ==> 
        result[i] >= stair_heights[0] && result[i] >= stair_heights[boxes[i].0 - 1]) &&
    (forall i :: 0 <= i < |boxes| ==> 
        result[i] == max(if i == 0 then stair_heights[0] else result[i-1] + boxes[i-1].1, 
                        stair_heights[boxes[i].0 - 1]))
}

method solve(stairs_amount: int, stair_heights: seq<int>, boxes_amount: int, boxes: seq<(int, int)>) returns (result: seq<int>)
    requires stairs_amount >= 1
    requires |stair_heights| == stairs_amount
    requires boxes_amount >= 0
    requires |boxes| == boxes_amount
    requires ValidStairs(stair_heights)
    requires ValidBoxes(boxes, stairs_amount)
    ensures ValidResult(result, boxes, stair_heights)
{
    var current_stair_heights := stair_heights;
    var landing_heights: seq<int> := [];

    for i := 0 to boxes_amount
        invariant |landing_heights| == i
        invariant |current_stair_heights| == stairs_amount
        invariant forall j :: 0 <= j < i ==> landing_heights[j] >= 0
        invariant forall j :: 0 <= j < i ==> 
            landing_heights[j] >= stair_heights[0] && landing_heights[j] >= stair_heights[boxes[j].0 - 1]
        invariant forall j :: 0 <= j < i ==> 
            landing_heights[j] == max(if j == 0 then stair_heights[0] else landing_heights[j-1] + boxes[j-1].1,
                                     stair_heights[boxes[j].0 - 1])
        invariant i > 0 ==> current_stair_heights[0] == landing_heights[i-1] + boxes[i-1].1
        invariant forall j :: 1 <= j < stairs_amount ==> current_stair_heights[j] == stair_heights[j]
        invariant forall j :: 0 <= j < stairs_amount ==> current_stair_heights[j] >= 0
        invariant i == 0 ==> current_stair_heights[0] == stair_heights[0]
    {
        var width := boxes[i].0;
        var height := boxes[i].1;

        var box_bottom := max(current_stair_heights[0], stair_heights[width - 1]);

        landing_heights := landing_heights + [box_bottom];

        assert landing_heights[i] == box_bottom;

        if i == 0 {
            assert current_stair_heights[0] == stair_heights[0];
            assert box_bottom == max(stair_heights[0], stair_heights[boxes[i].0 - 1]);
        } else {
            assert current_stair_heights[0] == landing_heights[i-1] + boxes[i-1].1;
            assert box_bottom == max(landing_heights[i-1] + boxes[i-1].1, stair_heights[boxes[i].0 - 1]);
        }

        current_stair_heights := current_stair_heights[0 := box_bottom + height];
    }

    return landing_heights;
}
