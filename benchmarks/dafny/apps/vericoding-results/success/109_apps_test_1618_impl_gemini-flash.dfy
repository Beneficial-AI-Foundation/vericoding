// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 3): Ensured loop invariant for k=0 by initializing current_val with the max of initial stair height and required stair height. */
{
  var res_seq: seq<int> := [];

  if boxes_amount == 0 {
    return res_seq;
  }

  var i := 0;
  while i < boxes_amount
    invariant 0 <= i <= boxes_amount
    invariant |res_seq| == i
    invariant forall k :: 0 <= k < i ==> res_seq[k] >= 0
    invariant forall k :: 0 <= k < i ==> res_seq[k] >= stair_heights[0] && res_seq[k] >= stair_heights[boxes[k].0 - 1]
    invariant forall k :: 0 <= k < i ==> (k == 0 ==> res_seq[k] == max(stair_heights[0], stair_heights[boxes[k].0 - 1])) && (k > 0 ==> res_seq[k] == max(res_seq[k-1] + boxes[k-1].1, stair_heights[boxes[k].0 - 1]))
    decreases boxes_amount - i
  {
    var current_val: int;
    if i == 0 {
      current_val := max(stair_heights[0], stair_heights[boxes[i].0 - 1]);
    } else {
      current_val := max(res_seq[i-1] + boxes[i-1].1, stair_heights[boxes[i].0 - 1]);
    }
    res_seq := res_seq + [current_val];
    i := i + 1;
  }

  return res_seq;
}
// </vc-code>
