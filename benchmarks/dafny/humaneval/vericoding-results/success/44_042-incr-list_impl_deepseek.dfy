// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function AddOne(x: int): int { x + 1 }
// </vc-helpers>

// <vc-spec>
method incr_list(l: seq<int>) returns (result: seq<int>)

    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added helper and fixed indexing */
{
  result := [];
  var i := 0;
  while i < |l|
    invariant |result| == i
    invariant 0 <= i <= |l|
    invariant forall j :: 0 <= j < i ==> result[j] == l[j] + 1
  {
    result := result + [AddOne(l[i])];
    i := i + 1;
  }
}
// </vc-code>
