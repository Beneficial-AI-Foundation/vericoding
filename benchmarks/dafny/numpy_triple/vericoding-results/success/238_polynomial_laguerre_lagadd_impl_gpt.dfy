// <vc-preamble>
// Add one Laguerre series to another
// Performs component-wise addition of two Laguerre series coefficients
// with zero padding for the shorter sequence
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced 'function method' with 'function' to satisfy syntax and provide zero-padded accessor */
function paddedAt(c: seq<real>, i: int): real
  requires 0 <= i
{
  if i < |c| then c[i] else 0.0
}
// </vc-helpers>

// <vc-spec>
method lagadd(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  // The result length is the maximum of the input lengths
  ensures |result| == (if |c1| >= |c2| then |c1| else |c2|)
  
  // Component-wise addition with zero padding
  ensures forall i :: 0 <= i < |result| ==>
    result[i] == (if i < |c1| then c1[i] else 0.0) + 
                 (if i < |c2| then c2[i] else 0.0)
  
  // Non-empty inputs produce non-empty output
  ensures (|c1| > 0 || |c2| > 0) ==> |result| > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented component-wise addition with zero padding using a loop and invariants */
{
  var n := if |c1| >= |c2| then |c1| else |c2|;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a.Length == n
    invariant forall j :: 0 <= j < i ==> a[j] == paddedAt(c1, j) + paddedAt(c2, j)
    decreases n - i
  {
    a[i] := paddedAt(c1, i) + paddedAt(c2, i);
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
