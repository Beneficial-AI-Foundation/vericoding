// <vc-preamble>
// Method to subtract one Laguerre series from another
// Input sequences can have different lengths; shorter sequences are implicitly padded with zeros
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple max helper retained to express maximum length calculations */
function Max(a: int, b: int): int {
  if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method Lagsub(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    ensures |result| == if |c1| >= |c2| then |c1| else |c2|  // Result length is max of input lengths
    // Component-wise subtraction with implicit zero-padding: result[i] = (c1[i] or 0) - (c2[i] or 0)
    ensures forall i :: 0 <= i < |result| ==> 
        result[i] == (if i < |c1| then c1[i] else 0.0) - (if i < |c2| then c2[i] else 0.0)
    // The difference of two Laguerre series is a Laguerre series
    // (this is a mathematical property of Laguerre polynomials - subtraction preserves the basis)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fill array iteratively to avoid initializer index proof issues */
  var n := if |c1| >= |c2| then |c1| else |c2|;
  var a := new real[n];
  var j := 0;
  while j < n
    invariant a.Length == n
    invariant 0 <= j <= n
    invariant forall i :: 0 <= i < j ==> a[i] == (if i < |c1| then c1[i] else 0.0) - (if i < |c2| then c2[i] else 0.0)
  {
    var v1 := if j < |c1| then c1[j] else 0.0;
    var v2 := if j < |c2| then c2[j] else 0.0;
    a[j] := v1 - v2;
    j := j + 1;
  }
  result := a[..];
}
// </vc-code>
