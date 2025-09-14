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
lemma MinMoves_nonneg(a: int, b: int)
    requires a >= 1 && b >= 1
    ensures MinMoves(a, b) >= 0
{
    if a == b {
        assert MinMoves(a, b) == 0;
    } else if a < b {
        if (b - a) % 2 == 1 {
            assert MinMoves(a, b) == 1;
        } else {
            assert MinMoves(a, b) == 2;
        }
    } else {
        if (a - b) % 2 == 0 {
            assert MinMoves(a, b) == 1;
        } else {
            assert MinMoves(a, b) == 2;
        }
    }
    assert MinMoves(a, b) >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<(int, int)>) returns (result: seq<int>)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
  var n := |input|;
  var arr := new int[n];
  var i := 0;
  // invariants to help verification
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> arr[k] == MinMoves(input[k].0, input[k].1)
    invariant forall k :: 0 <= k < i ==> arr[k] >= 0
    invariant forall j :: 0 <= j < n ==> input[j].0 >= 1 && input[j].1 >= 1
  {
    arr[i] := MinMoves(input[i].0, input[i].1);
    MinMoves_nonneg(input[i].0, input[i].1);
    i := i + 1;
  }
  // after the loop, establish full properties to help the postcondition
  assert i == n;
  assert forall k :: 0 <= k < n ==> arr[k] == MinMoves(input[k].0, input[k].1);
  assert forall k :: 0 <= k < n ==> arr[k] >= 0;
  result := arr[..];
  assert |result| == n;
  assert forall k :: 0 <= k < |result| ==> result[k] >= 0;
  assert forall k :: 0 <= k < |input| ==> result[k] == MinMoves(input[k].0, input[k].1);
}
// </vc-code>

