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
lemma {:induction false} MaxIsAssociative(a:int, b:int, c:int)
  ensures max(max(a, b), c) == max(a, max(b, c))
{
}

lemma {:induction false} MaxIsIdempotent(a:int, b:int)
  ensures max(max(a, b), b) == max(a, b)
{
}

lemma {:induction false} MaxCommutes(a:int, b:int)
  ensures max(a, b) == max(b, a)
{
}

predicate NonDecreasingSequence(a: seq<int>)
{
  |a| >= 1 && forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i + 1]
}

lemma {:induction false} NonDecreasingSequenceLemma(a: seq<int>, i: int, j: int)
  requires |a| >= 1
  requires NonDecreasingSequence(a)
  requires 0 <= i <= j < |a|
  ensures a[i] <= a[j]
{
}

lemma {:induction false} ValidResultPrefixLemma(result: seq<int>, boxes: seq<(int, int)>, stair_heights: seq<int>, i: int)
  requires |stair_heights| >= 1
  requires forall k :: 0 <= k < |boxes| ==> boxes[k].0 >= 1 && boxes[k].0 <= |stair_heights|
  requires ValidResult(result, boxes, stair_heights)
  requires 0 <= i <= |boxes|
  ensures ValidResult(result[0..i], boxes[0..i], stair_heights)
{
}

lemma {:induction false} ValidResultSingletonLemma(box: (int, int), stair_heights: seq<int>)
  requires |stair_heights| >= 1
  requires box.0 >= 1 && box.0 <= |stair_heights|
  ensures ValidResult([max(stair_heights[0], stair_heights[box.0 - 1])], [box], stair_heights)
{
}

lemma {:induction false} CurrentHeightLemma(result: seq<int>, boxes: seq<(int, int)>, stair_heights: seq<int>, box_index: int, current_height: int)
  requires |stair_heights| >= 1
  requires forall k :: 0 <= k < |boxes| ==> boxes[k].0 >= 1 && boxes[k].0 <= |stair_heights|
  requires 0 <= box_index <= |boxes|
  requires |result| == box_index
  requires current_height >= stair_heights[0]
  requires box_index > 0 ==> current_height == result[box_index - 1] + boxes[box_index - 1].1
  requires forall i :: 0 <= i < box_index ==> 
        result[i] == max(if i == 0 then stair_heights[0] else result[i-1] + boxes[i-1].1, 
                        stair_heights[boxes[i].0 - 1])
  ensures box_index == |boxes| ==> ValidResult(result, boxes, stair_heights)
{
  if box_index == |boxes| {
    assert |result| == |boxes|;

    forall i | 0 <= i < |boxes| 
      ensures result[i] >= 0
    {
      if i == 0 {
        assert result[i] >= stair_heights[0] && stair_heights[0] >= 0;
      }
    }

    forall i | 0 <= i < |boxes| 
      ensures result[i] >= stair_heights[0] && result[i] >= stair_heights[boxes[i].0 - 1]
    {
      assert result[i] == max(if i == 0 then stair_heights[0] else result[i-1] + boxes[i-1].1, 
                            stair_heights[boxes[i].0 - 1]);
    }
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
  result := [];
  var current_height := stair_heights[0];
  var box_index := 0;
  
  while box_index < boxes_amount
    invariant 0 <= box_index <= boxes_amount
    invariant |result| == box_index
    invariant current_height >= stair_heights[0]
    invariant box_index > 0 ==> current_height == result[box_index - 1] + boxes[box_index - 1].1
    invariant forall i :: 0 <= i < box_index ==> result[i] >= 0
    invariant forall i :: 0 <= i < box_index ==> 
        result[i] >= stair_heights[0] && result[i] >= stair_heights[boxes[i].0 - 1]
    invariant forall i :: 0 <= i < box_index ==> 
        result[i] == max(if i == 0 then stair_heights[0] else result[i-1] + boxes[i-1].1, 
                        stair_heights[boxes[i].0 - 1])
  {
    var stair_index := boxes[box_index].0 - 1;
    var required_height := max(current_height, stair_heights[stair_index]);
    
    result := result + [required_height];
    
    assert required_height >= 0 by {
      if box_index == 0 {
        assert required_height >= stair_heights[0] >= 0;
      } else {
        assert current_height >= stair_heights[0] >= 0;
        assert stair_heights[stair_index] >= 0;
      }
    };
    
    assert required_height >= stair_heights[0];
    assert required_height >= stair_heights[stair_index];
    
    if box_index == 0 {
      assert required_height == max(stair_heights[0], stair_heights[stair_index]);
    } else {
      assert required_height == max(result[box_index - 1] + boxes[box_index - 1].1, stair_heights[stair_index]);
    }
    
    current_height := required_height + boxes[box_index].1;
    box_index := box_index + 1;
    
    if box_index < boxes_amount {
      assert current_height >= stair_heights[0] by {
        assert required_height >= stair_heights[0];
        assert boxes[box_index - 1].1 >= 1;
      }
    }
  }
  
  CurrentHeightLemma(result, boxes, stair_heights, box_index, current_height);
}
// </vc-code>

