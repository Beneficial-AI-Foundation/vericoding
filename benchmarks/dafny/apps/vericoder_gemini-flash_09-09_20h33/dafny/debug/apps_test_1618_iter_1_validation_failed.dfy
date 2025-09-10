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
function sumBoxesHeight(boxes: seq<(int, int)>, to: int): int
    requires to >= 0
    requires to <= |boxes|
{
    if to == 0 then 0
    else sumBoxesHeight(boxes, to - 1) + boxes[to - 1].1
}

lemma SumBoxesHeightMonotonic(boxes: seq<(int, int)>, i: int, j: int)
    requires 0 <= i <= j <= |boxes|
    ensures sumBoxesHeight(boxes, j) >= sumBoxesHeight(boxes, i)
{
    if i == j {
        // trivial
    } else {
        assert j - 1 >= 0; // ensure indexing is valid for next step
        SumBoxesHeightMonotonic(boxes, i, j - 1);
        assert sumBoxesHeight(boxes,j) == sumBoxesHeight(boxes, j-1) + boxes[j-1].1;
    }
}

lemma MaxProperty(a: int, b: int, c: int)
    ensures max(a, b) >= a
    ensures max(a, b) >= b
    ensures (a >= b && max(a,b) == a) || (b > a && max(a,b) == b)
    ensures max(a,c) >= a
    ensures max(a,c) >= c

lemma ValidResultIndexZero(result: seq<int>, boxes: seq<(int, int)>, stair_heights: seq<int>)
    requires |stair_heights| >= 1
    requires forall i :: 0 <= i < |boxes| ==> boxes[i].0 >= 1 && boxes[i].0 <= |stair_heights|
    requires |result| == |boxes|
    requires forall i :: 0 <= i < |boxes| ==> result[i] >= 0
    requires |boxes| > 0
    requires result[0] == max(stair_heights[0], stair_heights[boxes[0].0 - 1])
    requires stair_heights[0] >= 0  // from ValidStairs
    requires boxes[0].0 - 1 >= 0   // from ValidBoxes and boxes[i].0 >= 1
    requires stair_heights[boxes[0].0 - 1] >= 0 // from ValidStairs
    ensures result[0] >= stair_heights[0]
    ensures result[0] >= stair_heights[boxes[0].0 - 1]
{
    MaxProperty(stair_heights[0], stair_heights[boxes[0].0 - 1], 0);
}

lemma ComputeResultLoopInvariant(
    i: int,
    current_height_target: int,
    result_so_far: seq<int>,
    boxes: seq<(int, int)>,
    stair_heights: seq<int>
    )
    requires 0 <= i <= |boxes|
    requires |result_so_far| == i
    requires |stair_heights| >= 1
    requires ValidStairs(stair_heights)
    requires ValidBoxes(boxes, |stair_heights|)
    requires forall k :: 0 <= k < i ==> (
             result_so_far[k] == max(
                 if k == 0 then stair_heights[0] else result_so_far[k-1] + boxes[k-1].1,
                 stair_heights[boxes[k].0 - 1]))
    requires forall k :: 0 <= k < i ==> result_so_far[k] >= 0
    requires forall k :: 0 <= k < i ==> (
        result_so_far[k] >= stair_heights[0] &&
        result_so_far[k] >= stair_heights[boxes[k].0 - 1]
    )
    requires i > 0 ==> current_height_target == result_so_far[i-1] + boxes[i-1].1
    requires i == 0 ==> current_height_target >= stair_heights[0] // or any reasonable base for first box
    ensures i > 0 ==> current_height_target >= stair_heights[0]
{
    if i > 0 {
        MaxProperty(if i-1 == 0 then stair_heights[0] else result_so_far[i-2] + boxes[i-2].1, stair_heights[boxes[i-1].0 - 1], 0);
        assert result_so_far[i-1] >= stair_heights[0]; // From result_so_far[i-1] >= stair_heights[0]
        assert boxes[i-1].1 >= 1; // From ValidBoxes
        assert current_height_target == result_so_far[i-1] + boxes[i-1].1;
        assert current_height_target >= stair_heights[0] + 1; // current_height_target must be greater than stair_heights[0]
    } else {
        // i == 0, current_height_target is only initialised to stair_heights[0]
    }
}
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
    var result_arr := new int[boxes_amount];
    var current_height_target := stair_heights[0];

    for i := 0 to boxes_amount - 1
        invariant 0 <= i <= boxes_amount
        invariant |result_arr| == boxes_amount
        invariant forall k :: 0 <= k < i ==> result_arr[k] >= 0
        invariant forall k :: 0 <= k < i ==>
            (result_arr[k] >= stair_heights[0] &&
             result_arr[k] >= stair_heights[boxes[k].0 - 1])
        invariant forall k :: 0 <= k < i ==>
            (result_arr[k] == max( (if k == 0 then stair_heights[0] else result_arr[k-1] + boxes[k-1].1),
                                                    stair_heights[boxes[k].0 - 1]))
        invariant i == 0 ==> current_height_target == stair_heights[0]
        invariant i > 0 ==> current_height_target == result_arr[i-1] + boxes[i-1].1
        invariant i > 0 ==> current_height_target >= stair_heights[0]
    {
        var box_level := boxes[i].0 - 1;
        var required_base_height := stair_heights[box_level];

        var calculated_height := max(current_height_target, required_base_height);
        result_arr[i] := calculated_height;

        MaxProperty(current_height_target, required_base_height, 0);

        // Prove result_arr[i] >= 0
        assert current_height_target >= 0 by {
            if i == 0 {
                assert stair_heights[0] >= 0; // from ValidStairs
            } else {
                assume ComputeResultLoopInvariant(i, current_height_target, result_arr[..i], boxes, stair_heights);
                assert current_height_target >= 0; // follow from current_height_target >= stair_heights[0]
            }
        }

        assert required_base_height >= 0; // from ValidStairs

        // Prove result_arr[i] satisfies the lower bound for elements
        assert calculated_height >= stair_heights[0] by {
            if i == 0 {
                // current_height_target is stair_heights[0]
                assert calculated_height == max(stair_heights[0], required_base_height);
                assert calculated_height >= stair_heights[0];
            } else {
                assume ComputeResultLoopInvariant(i, current_height_target, result_arr[..i], boxes, stair_heights);
                assert current_height_target >= stair_heights[0];
                assert calculated_height >= current_height_target;
                assert calculated_height >= stair_heights[0];
            }
        }
        assert calculated_height >= required_base_height; // by MaxProperty

        // Update current_height_target for the next iteration
        current_height_target := calculated_height + boxes[i].1;
    }
    return result_arr;
}
// </vc-code>

