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
  var maxLen := if |c1| >= |c2| then |c1| else |c2|;
  result := [];
  var i := 0;
  while i < maxLen
    invariant 0 <= i <= maxLen
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> 
      result[j] == (if j < |c1| then c1[j] else 0.0) + (if j < |c2| then c2[j] else 0.0)
  {
    var val1 := if i < |c1| then c1[i] else 0.0;
    var val2 := if i < |c2| then c2[i] else 0.0;
    result := result + [val1 + val2];
    i := i + 1;
  }
}
// </vc-code>
