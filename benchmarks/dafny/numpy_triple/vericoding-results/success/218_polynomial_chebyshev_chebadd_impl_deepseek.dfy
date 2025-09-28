// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ZeroExtend(c: seq<real>, n: nat): (r: seq<real>)
  requires |c| <= n
  ensures |r| == n
  ensures forall i :: 0 <= i < |c| ==> r[i] == c[i]
  ensures forall i :: |c| <= i < n ==> r[i] == 0.0
{
  /* helper modified by LLM (iteration 4): Fixed multiplication syntax using seq construction */
  if n == 0 then [] else 
    seq(n, i requires 0 <= i < n => if i < |c| then c[i] else 0.0)
}
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
  /* code modified by LLM (iteration 4): Fixed to use ZeroExtend helper */
  var n := if |c1| >= |c2| then |c1| else |c2|;
  var e1 := ZeroExtend(c1, n);
  var e2 := ZeroExtend(c2, n);
  result := seq(n, i requires 0 <= i < n => e1[i] + e2[i]);
}
// </vc-code>
