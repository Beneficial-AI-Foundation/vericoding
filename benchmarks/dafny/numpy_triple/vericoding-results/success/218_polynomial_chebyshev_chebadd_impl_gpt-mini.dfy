// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max(a: nat, b: nat): nat { if a >= b then a else b }
// </vc-helpers>

// <vc-spec>
method ChebyshevAdd(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    // No preconditions - function accepts any coefficient sequences
    ensures |result| == if |c1| >= |c2| then |c1| else |c2|
    // For each index in the result, the value is determined by coefficient-wise addition
    ensures forall i :: 0 <= i < |result| ==>
        result[i] == (if i < |c1| then c1[i] else 0.0) + 
                     (if i < |c2| then c2[i] else 0.0)
    // Result preserves non-zero coefficients from first input
    ensures forall i :: 0 <= i < |c1| && c1[i] != 0.0 ==>
        result[i] == c1[i] + (if i < |c2| then c2[i] else 0.0)
    // Result preserves non-zero coefficients from second input  
    ensures forall i :: 0 <= i < |c2| && c2[i] != 0.0 ==>
        result[i] == (if i < |c1| then c1[i] else 0.0) + c2[i]
// </vc-spec>
// <vc-code>
{
  var m := Max(|c1|, |c2|);
  var a := new real[m];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant forall j :: 0 <= j < i ==> a[j] == (if j < |c1| then c1[j] else 0.0) + (if j < |c2| then c2[j] else 0.0)
  {
    var v1 := if i < |c1| then c1[i] else 0.0;
    var v2 := if i < |c2| then c2[i] else 0.0;
    a[i] := v1 + v2;
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
