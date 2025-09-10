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
lemma MaxProperties(a: int, b: int)
    ensures max(a, b) >= a
    ensures max(a, b) >= b
    ensures max(a, b) == a || max(a, b) == b
{
}

lemma ValidResultLemma(result: seq<int>, boxes: seq<(int, int)>, stair_heights: seq<int>, i: int)
    requires |stair_heights| >= 1
    requires forall j :: 0 <= j < |boxes| ==> boxes[j].0 >= 1 && boxes[j].0 <= |stair_heights|
    requires 0 <= i < |boxes|
    requires |result| == i + 1
    requires forall j :: 0 <= j < i + 1 ==> result[j] >= 0
    requires forall j :: 0 <= j < i + 1 ==> 
        result[j] >= stair_heights[0] && result[j] >= stair_heights[boxes[j].0 - 1]
    requires forall j :: 0 <= j < i + 1 ==> 
        result[j] == max(if j == 0 then stair_heights[0] else result[j-1] + boxes[j-1].1, 
                        stair_heights[boxes[j].0 - 1])
    ensures ValidResult(result, boxes[..i+1], stair_heights)
{
    assert |boxes[..i+1]| == i + 1;
    assert boxes[..i+1] == boxes[0..i+1];
    assert forall j :: 0 <= j < i + 1 ==> boxes[..i+1][j] == boxes[j];
}

lemma ValidResultComplete(result: seq<int>, boxes: seq<(int, int)>, stair_heights: seq<int>)
    requires |stair_heights| >= 1
    requires forall j :: 0 <= j < |boxes| ==> boxes[j].0 >= 1 && boxes[j].0 <= |stair_heights|
    requires |result| == |boxes|
    requires forall j :: 0 <= j < |boxes| ==> result[j] >= 0
    requires forall j :: 0 <= j < |boxes| ==> 
        result[j] >= stair_heights[0] && result[j] >= stair_heights[boxes[j].0 - 1]
    requires forall j :: 0 <= j < |boxes| ==> 
        result[j] == max(if j == 0 then stair_heights[0] else result[j-1] + boxes[j-1].1, 
                        stair_heights[boxes[j].0 - 1])
    ensures ValidResult(result, boxes, stair_heights)
{
}

lemma LoopInvariantMaintained(result: seq<int>, boxes: seq<(int, int)>, stair_heights: seq<int>, i: int, new_height: int)
    requires |stair_heights| >= 1
    requires forall j :: 0 <= j < |boxes| ==> boxes[j].0 >= 1 && boxes[j].0 <= |stair_heights|
    requires 0 <= i < |boxes|
    requires |result| == i
    requires forall j :: 0 <= j < i ==> result[j] >= 0
    requires forall j :: 0 <= j < i ==> 
        result[j] >= stair_heights[0] && result[j] >= stair_heights[boxes[j].0 - 1]
    requires forall j :: 0 <= j < i ==> 
        result[j] == max(if j == 0 then stair_heights[0] else result[j-1] + boxes[j-1].1, 
                        stair_heights[boxes[j].0 - 1])
    requires new_height == max(if i == 0 then stair_heights[0] else result[i-1] + boxes[i-1].1, 
                              stair_heights[boxes[i].0 - 1])
    ensures var new_result := result + [new_height];
            forall j :: 0 <= j < i + 1 ==> 
                new_result[j] == max(if j == 0 then stair_heights[0] else new_result[j-1] + boxes[j-1].1, 
                                   stair_heights[boxes[j].0 - 1])
{
    var new_result := result + [new_height];
    
    forall j | 0 <= j < i + 1
        ensures new_result[j] == max(if j == 0 then stair_heights[0] else new_result[j-1] + boxes[j-1].1, 
                                   stair_heights[boxes[j].0 - 1])
    {
        if j < i {
            assert new_result[j] == result[j];
            if j > 0 {
                assert new_result[j-1] == result[j-1];
                assert new_result[j] == max(stair_heights[0], stair_heights[boxes[j].0 - 1]) || 
                       new_result[j] == max(new_result[j-1] + boxes[j-1].1, stair_heights[boxes[j].0 - 1]);
            } else {
                assert j == 0;
                assert new_result[j] == max(stair_heights[0], stair_heights[boxes[j].0 - 1]);
            }
        } else {
            assert j == i;
            assert new_result[j] == new_height;
            if i == 0 {
                assert new_height == max(stair_heights[0], stair_heights[boxes[i].0 - 1]);
            } else {
                assert new_height == max(result[i-1] + boxes[i-1].1, stair_heights[boxes[i].0 - 1]);
                assert new_result[i-1] == result[i-1];
            }
        }
    }
}

lemma EmptyBoxesValid(stair_heights: seq<int>)
    requires |stair_heights| >= 1
    ensures ValidResult([], [], stair_heights)
{
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
    result := [];
    
    if boxes_amount == 0 {
        EmptyBoxesValid(stair_heights);
        return;
    }
    
    var i := 0;
    while i < boxes_amount
        invariant 0 <= i <= boxes_amount
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] >= 0
        invariant forall j :: 0 <= j < i ==> 
            result[j] >= stair_heights[0] && result[j] >= stair_heights[boxes[j].0 - 1]
        invariant forall j :: 0 <= j < i ==> 
            result[j] == max(if j == 0 then stair_heights[0] else result[j-1] + boxes[j-1].1, 
                            stair_heights[boxes[j].0 - 1])
        invariant i > 0 ==> ValidResult(result, boxes[..i], stair_heights)
    {
        var prev_height := if i == 0 then stair_heights[0] else result[i-1] + boxes[i-1].1;
        var stair_height := stair_heights[boxes[i].0 - 1];
        var new_height := max(prev_height, stair_height);
        
        MaxProperties(prev_height, stair_height);
        LoopInvariantMaintained(result, boxes, stair_heights, i, new_height);
        
        result := result + [new_height];
        
        assert result[i] == new_height;
        assert result[i] >= 0;
        assert result[i] >= stair_heights[0];
        assert result[i] >= stair_heights[boxes[i].0 - 1];
        assert result[i] == max(if i == 0 then stair_heights[0] else result[i-1] + boxes[i-1].1, 
                               stair_heights[boxes[i].0 - 1]);
        
        i := i + 1;
        
        ValidResultLemma(result, boxes, stair_heights, i - 1);
    }
    
    assert ValidResult(result, boxes[..boxes_amount], stair_heights);
    assert boxes[..boxes_amount] == boxes;
    ValidResultComplete(result, boxes, stair_heights);
}
// </vc-code>

