predicate ValidInput(input: seq<(int, int)>)
{
    forall i :: 0 <= i < |input| ==> input[i].0 >= 1 && input[i].1 >= 1
}

function MinMoves(a: int, b: int): int
    requires a >= 1 && b >= 1
{
    if a == b then 0
    else if a < b then
        if (b - a) % 2 == 1 then 1 else 2
    else
        if (a - b) % 2 == 0 then 1 else 2
}

predicate ValidOutput(input: seq<(int, int)>, result: seq<int>)
    requires ValidInput(input)
{
    |result| == |input| &&
    forall i :: 0 <= i < |input| ==> result[i] == MinMoves(input[i].0, input[i].1) &&
    forall i :: 0 <= i < |result| ==> result[i] >= 0
}

// <vc-helpers>
lemma MinMovesNonNegative(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures MinMoves(a, b) >= 0
{
  if a == b {
    assert MinMoves(a, b) == 0;
  } else if a < b {
    if ((b - a) % 2) == 1 {
      assert MinMoves(a, b) == 1;
    } else {
      assert MinMoves(a, b) == 2;
    }
  } else {
    if ((a - b) % 2) == 0 {
      assert MinMoves(a, b) == 1;
    } else {
      assert MinMoves(a, b) == 2;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<(int, int)>) returns (result: seq<int>)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i := 0;
  while i < |input|
    invariant 0 <= i <= |input|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == MinMoves(input[j].0, input[j].1)
    invariant forall j :: 0 <= j < |res| ==> res[j] >= 0
    decreases |input| - i
  {
    var a := input[i].0;
    var b := input[i].1;
    assert a >= 1 && b >= 1;
    res := res + [MinMoves(a, b)];
    MinMovesNonNegative(a, b);
    i := i + 1;
  }
  result := res;
  assert i >= |input|;
  assert i == |input|;
  assert |result| == |input|;
  assert forall k :: 0 <= k < |input| ==> result[k] == MinMoves(input[k].0, input[k].1);
  assert forall k :: 0 <= k < |result| ==> result[k] >= 0;
}
// </vc-code>

