// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): handle empty sequence case to avoid division by zero */
  if |l| == 0 {
    r := [];
  } else {
    r := seq(|l|, i => l[(i - n + |l|) % |l|]);
  }
}
// </vc-code>
