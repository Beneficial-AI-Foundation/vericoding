// <vc-preamble>
// Helper function to compute maximum of two integers
function Max(a: int, b: int): int
{
    if a >= b then a else b
}

/**
 * Subtract one Hermite series from another.
 * Returns the difference of two Hermite series c1 - c2.
 * The sequences of coefficients are from lowest order term to highest.
 * Shorter arrays are implicitly padded with zeros for subtraction.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix duplicate Max function */
function MaxHelper(a: int, b: int): int {
    if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method hermesub(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    // The result length equals the maximum of input lengths
    ensures |result| == Max(|c1|, |c2|)
    // Each coefficient is the component-wise difference, with implicit zero padding
    ensures forall i :: 0 <= i < |result| ==>
        result[i] == (if i < |c1| then c1[i] else 0.0) - (if i < |c2| then c2[i] else 0.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fix array/seq conversion issues */
{
  var length := MaxHelper(|c1|, |c2|);
  var arr := new real[length];
  var i := 0;
  while i < length
    invariant 0 <= i <= length
    invariant arr.Length == length
    invariant forall j :: 0 <= j < i ==> arr[j] == (if j < |c1| then c1[j] else 0.0) - (if j < |c2| then c2[j] else 0.0)
  {
    var val1 := if i < |c1| then c1[i] else 0.0;
    var val2 := if i < |c2| then c2[i] else 0.0;
    arr[i] := val1 - val2;
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>
