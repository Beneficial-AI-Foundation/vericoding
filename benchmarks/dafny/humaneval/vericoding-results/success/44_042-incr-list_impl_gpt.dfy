// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple increment function used during sequence construction */
function PlusOne(x: int): int { x + 1 }
// </vc-helpers>

// <vc-spec>
method incr_list(l: seq<int>) returns (result: seq<int>)

    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): construct the incremented sequence via iterative concatenation with invariants */
  var r: seq<int> := [];
  var i: int := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == l[j] + 1
    decreases |l| - i
  {
    r := r + [PlusOne(l[i])];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
