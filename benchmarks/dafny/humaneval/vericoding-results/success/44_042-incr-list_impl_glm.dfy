// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method incr_list(l: seq<int>) returns (result: seq<int>)

    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fixed type error by building sequence with appending instead of array assignment */
  var len := |l|;
  result := [];
  for i := 0 to len
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == l[j] + 1
  {
    result := result + [l[i] + 1];
  }
}
// </vc-code>
