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
lemma max_ge_a(a:int, b:int)
  ensures max(a, b) >= a
{
  if a >= b {
    assert max(a,b) == a;
  } else {
    assert max(a,b) == b;
    assert b >= a;
  }
}

lemma max_ge_b(a:int, b:int)
  ensures max(a, b) >= b
{
  if a >= b {
    assert max(a,b) == a;
    assert a >= b;
  } else {
    assert max(a,b) == b;
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
  var res: seq<int> := [];
  var i: int := 0;
  var cur: int := stair_heights[0];
  while i < |boxes|
    invariant 0 <= i <= |boxes|
    invariant |res| == i
    invariant cur == (if i == 0 then stair_heights[0] else res[i-1] + boxes[i-1].1)
    invariant cur >= stair_heights[0]
    invariant forall j :: 0 <= j < i ==> boxes[j].0 >= 1
    invariant forall j :: 0 <= j < i ==> boxes[j].0 <= stairs_amount
    invariant forall j :: 0 <= j < i ==> res[j] >= 0
    invariant forall j :: 0 <= j < i ==> res[j] >= stair_heights[0]
    invariant forall j :: 0 <= j < i ==> res[j] >= stair_heights[boxes[j].0 - 1]
    invariant forall j :: 0 <= j < i ==>
      res[j] == max((if j == 0 then stair_heights[0] else res[j-1] + boxes[j-1].1),
                    stair_heights[boxes[j].0 - 1])
    decreases |boxes| - i
  {
    assert 0 <= i < |boxes|;
    assert boxes[i].0 >= 1;
    assert boxes[i].0 <= stairs_amount;
    assert 0 <= boxes[i].0 - 1;
    assert boxes[i].0 - 1 < |stair_heights|;
    var s := stair_heights[boxes[i].0 - 1];
    var v := max(cur, s);
    max_ge_a(cur, s);
    max_ge_b(cur, s);

    var i0 := i;
    var r0 := res;

    res := res + [v];
    assert |r0| == i0;
    assert res[i0] == v;

    assert v >= cur;
    assert v >= s;

    assert cur == (if i0 == 0 then stair_heights[0] else r0[i0-1] + boxes[i0-1].1);
    if i0 > 0 {
      assert r0[i0-1] == res[i0-1];
    }
    assert cur == (if i0 == 0 then stair_heights[0] else res[i0-1] + boxes[i0-1].1);
    assert res[i0] == max((if i0 == 0 then stair_heights[0] else res[i0-1] + boxes[i0-1].1),
                          stair_heights[boxes[i0].0 - 1]);
    assert res[i0] >= stair_heights[0];
    assert res[i0] >= stair_heights[boxes[i0].0 - 1];
    assert res[i0] >= 0;

    assert boxes[i].1 >= 1;
    cur := v + boxes[i].1;
    i := i + 1;
    assert cur == res[i-1] + boxes[i-1].1;
  }
  result := res;
}
// </vc-code>

