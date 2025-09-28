// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): twoComp function */
function twoComp(a: int): int { -(a + 1) }

/* helper modified by LLM (iteration 4): Lemma relating sign of a and twoComp(a) for non -1 and nonzero inputs */
lemma TwoCompSignNonZero(a: int)
  requires a != -1 && a != 0
  ensures (a > 0) <==> (twoComp(a) < 0)
{
  // Unfold definition
  assert twoComp(a) == -(a + 1);
  // twoComp(a) < 0 <==> -(a+1) < 0 <==> a+1 > 0
  assert (twoComp(a) < 0) <==> (a + 1 > 0);
  // For integers, a+1 > 0 <==> a > -1
  assert (a + 1 > 0) <==> (a > -1);
  // From a != -1, a > -1 <==> a >= 0
  assert (a > -1) <==> (a >= 0);
  // From a != 0, a >= 0 <==> a > 0
  assert (a >= 0) <==> (a > 0);
  // Chain the equivalences to conclude the lemma's postcondition
  assert (a > 0) <==> (twoComp(a) < 0);
}

// </vc-helpers>

// <vc-spec>
method invert(x: seq<int>) returns (result: seq<int>)
  // The result has the same length as the input
  ensures |result| == |x|
  // Each element follows the two's complement relationship: ~x = -(x + 1)  
  ensures forall i :: 0 <= i < |x| ==> result[i] == -(x[i] + 1)
  // Identity property for zero
  ensures forall i :: 0 <= i < |x| ==> x[i] == 0 ==> result[i] == -1
  // Identity property for negative one
  ensures forall i :: 0 <= i < |x| ==> x[i] == -1 ==> result[i] == 0
  // Sign flipping property
  ensures forall i :: 0 <= i < |x| ==> x[i] != -1 ==> (x[i] > 0 <==> result[i] < 0)
  // Identity properties follow from the main relationship:
  // When x[i] == 0: result[i] == -(0 + 1) == -1
  // When x[i] == -1: result[i] == -(-1 + 1) == 0
  // Sign flipping: when x[i] != -1, x[i] > 0 <==> result[i] < 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): implement invert using twoComp and loop, invoking lemma for sign relation when applicable */
  var n := |x|;
  var a := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == twoComp(x[j])
    invariant forall j :: 0 <= j < i && x[j] != -1 && x[j] != 0 ==> (x[j] > 0 <==> a[j] < 0)
  {
    a[i] := twoComp(x[i]);
    if x[i] != -1 && x[i] != 0 {
      TwoCompSignNonZero(x[i]);
    }
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
