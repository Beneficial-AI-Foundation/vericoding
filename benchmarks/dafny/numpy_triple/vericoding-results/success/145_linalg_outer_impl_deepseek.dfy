// <vc-preamble>
// Method to compute the outer product of two vectors
// Given vectors a and b, produces a matrix where result[i][j] = a[i] * b[j]
// </vc-preamble>

// <vc-helpers>
function multiply(x: real, y: real): real { x * y }

function createRow(value: real, count: int): seq<real>
  requires count >= 0
  ensures |createRow(value, count)| == count
  ensures forall j :: 0 <= j < count ==> createRow(value, count)[j] == value
{
  if count == 0 then []
  else [value] + createRow(value, count - 1)
}

/* helper modified by LLM (iteration 5): Fixed createRowWithB to handle b indexing */
function createRowWithB(a_i: real, b: seq<real>): seq<real>
  requires |b| >= 0
  ensures |createRowWithB(a_i, b)| == |b|
  ensures forall j :: 0 <= j < |b| ==> createRowWithB(a_i, b)[j] == a_i * b[j]
{
  if |b| == 0 then []
  else [a_i * b[0]] + createRowWithB(a_i, b[1..])
}
// </vc-helpers>

// <vc-spec>
method outer(a: seq<real>, b: seq<real>) returns (result: seq<seq<real>>)
  requires |a| >= 0
  requires |b| >= 0
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |b|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |b| ==> result[i][j] == a[i] * b[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed loop indexing to use integer indices */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |b|
    invariant forall k, j :: 0 <= k < i && 0 <= j < |b| ==> result[k][j] == a[k] * b[j]
  {
    var row := createRowWithB(a[i], b);
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
