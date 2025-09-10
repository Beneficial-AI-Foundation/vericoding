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

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stairs_amount: int, stair_heights: seq<int>, boxes_amount: int, boxes: seq<(int, int)>) returns (result: seq<int>)
    requires stairs_amount >= 1
    requires |stair_heights| == stairs_amount
    requires boxes_amount >= 0
    requires |boxes| == boxes_amount
    requires ValidStairs(stair_heights)
    requires ValidBoxes(boxes, stairs_amount)
    ensures ValidResult(result, boxes, stair_heights)
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    while i < |boxes|
        invariant 0 <= i <= |boxes|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] >= stair_heights[0]
        invariant forall j :: 0 <= j < i ==> result[j] >= stair_heights[boxes[j].0 - 1]
        invariant forall j :: 0 <= j < i ==> 
            result[j] == max(if j == 0 then stair_heights[0] else result[j-1] + boxes[j-1].1, 
                             stair_heights[boxes[j].0 - 1])
    {
        var candidate1 := if i == 0 then stair_heights[0] else result[i - 1] + boxes[i - 1].1;
        var candidate2 := stair_heights[boxes[i].0 - 1];
        result := result + [max(candidate1, candidate2)];
        i := i + 1;
    }
}
// </vc-code>

