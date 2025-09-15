// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added decreases clause and implemented lemma proof */
predicate IsEven(x: int) { x % 2 == 0 }

function FindSmallestEven(nodes: seq<int>, start: int): (int, int)
  requires 0 <= start <= |nodes|
  requires forall i :: 0 <= i < |nodes| ==> nodes[i] >= 0
  decreases |nodes| - start
{
  if start >= |nodes| then (-1, -1)
  else if IsEven(nodes[start]) then
    var (restVal, restIdx) := FindSmallestEven(nodes, start + 1);
    if restIdx == -1 || nodes[start] <= restVal then (nodes[start], start)
    else (restVal, restIdx)
  else FindSmallestEven(nodes, start + 1)
}

lemma FindSmallestEvenCorrect(nodes: seq<int>, start: int)
  requires 0 <= start <= |nodes|
  requires forall i :: 0 <= i < |nodes| ==> nodes[i] >= 0
  ensures var (val, idx) := FindSmallestEven(nodes, start);
          (idx == -1) ==> (forall i :: start <= i < |nodes| ==> !IsEven(nodes[i]))
  ensures var (val, idx) := FindSmallestEven(nodes, start);
          (idx != -1) ==> (start <= idx < |nodes| && IsEven(nodes[idx]) && nodes[idx] == val)
  ensures var (val, idx) := FindSmallestEven(nodes, start);
          (idx != -1) ==> (forall i :: start <= i < |nodes| && IsEven(nodes[i]) ==> val <= nodes[i])
  ensures var (val, idx) := FindSmallestEven(nodes, start);
          (idx != -1) ==> (forall i :: start <= i < idx ==> !IsEven(nodes[i]) || nodes[i] > val)
  decreases |nodes| - start
{
  var (val, idx) := FindSmallestEven(nodes, start);
  if start >= |nodes| {
    return;
  }
  if IsEven(nodes[start]) {
    var (restVal, restIdx) := FindSmallestEven(nodes, start + 1);
    FindSmallestEvenCorrect(nodes, start + 1);
    if restIdx == -1 || nodes[start] <= restVal {
      assert val == nodes[start] && idx == start;
    } else {
      assert val == restVal && idx == restIdx;
    }
  } else {
    FindSmallestEvenCorrect(nodes, start + 1);
    assert val == FindSmallestEven(nodes, start + 1).0;
    assert idx == FindSmallestEven(nodes, start + 1).1;
  }
}
// </vc-helpers>

// <vc-spec>
method PluckSmallestEven(nodes: seq<int>) returns (result: seq<int>)

  requires |nodes| <= 10000
  requires forall i :: 0 <= i < |nodes| ==> nodes[i] >= 0

  ensures |result| == 0 || |result| == 2
  ensures |result| == 2 ==> 0 <= result[1] < |nodes| && nodes[result[1]] == result[0]
  ensures |result| == 2 ==> result[0] % 2 == 0
  ensures |result| == 2 ==> forall i :: 0 <= i < |nodes| && nodes[i] % 2 == 0 ==> result[0] <= nodes[i]
  ensures |result| == 2 ==> forall i :: 0 <= i < result[1] ==> nodes[i] % 2 != 0 || nodes[i] > result[0]
  ensures |result| == 0 ==> forall i :: 0 <= i < |nodes| ==> nodes[i] % 2 != 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added helper lemma call to establish postconditions */
  var (val, idx) := FindSmallestEven(nodes, 0);
  FindSmallestEvenCorrect(nodes, 0);
  
  if idx == -1 {
    result := [];
  } else {
    result := [val, idx];
  }
}
// </vc-code>
