// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 2): initialized min_val to fix definite-assignment errors */
  var min_idx: int := -1;
  var min_val: int := 0;

  var i := 0;
  while i < |nodes|
    invariant 0 <= i <= |nodes|
    invariant min_idx == -1 ==> (forall k :: 0 <= k < i ==> nodes[k] % 2 != 0)
    invariant min_idx != -1 ==> (
        0 <= min_idx < i &&
        nodes[min_idx] == min_val &&
        min_val % 2 == 0 &&
        (forall k :: 0 <= k < i && nodes[k] % 2 == 0 ==> min_val <= nodes[k]) &&
        (forall k :: 0 <= k < min_idx ==> nodes[k] % 2 != 0 || nodes[k] > min_val)
    )
  {
    if nodes[i] % 2 == 0 {
      if min_idx == -1 || nodes[i] < min_val {
        min_idx := i;
        min_val := nodes[i];
      }
    }
    i := i + 1;
  }

  if min_idx == -1 {
    result := [];
  } else {
    result := [min_val, min_idx];
  }
}
// </vc-code>
