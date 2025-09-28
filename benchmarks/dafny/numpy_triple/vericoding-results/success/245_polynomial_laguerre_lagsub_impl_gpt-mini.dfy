// <vc-preamble>
// Method to subtract one Laguerre series from another
// Input sequences can have different lengths; shorter sequences are implicitly padded with zeros
// </vc-preamble>

// <vc-helpers>
function max_len(a: seq<real>, b: seq<real>): int { if |a| >= |b| then |a| else |b| }
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
  var n := if |c1| >= |c2| then |c1| else |c2|;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == (if j < |c1| then c1[j] else 0.0) - (if j < |c2| then c2[j] else 0.0)
  {
    var x := if i < |c1| then c1[i] else 0.0;
    var y := if i < |c2| then c2[i] else 0.0;
    a[i] := x - y;
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
