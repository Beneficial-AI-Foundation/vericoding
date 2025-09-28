// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var n := if |c1| >= |c2| then |c1| else |c2|;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == (if k < |c1| then c1[k] else 0.0) + (if k < |c2| then c2[k] else 0.0)
  {
    var v1 := if i < |c1| then c1[i] else 0.0;
    var v2 := if i < |c2| then c2[i] else 0.0;
    result := result + [v1 + v2];
    i := i + 1;
  }
}
// </vc-code>
