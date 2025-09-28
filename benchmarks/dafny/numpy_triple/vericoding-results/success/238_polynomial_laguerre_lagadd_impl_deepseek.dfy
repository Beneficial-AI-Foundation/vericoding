// <vc-preamble>
// Add one Laguerre series to another
// Performs component-wise addition of two Laguerre series coefficients
// with zero padding for the shorter sequence
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a >= b then a else b }

predicate ValidIndex(i: int, s: seq<real>) {
  0 <= i < |s|
}

function GetValue(s: seq<real>, i: int): real
  requires 0 <= i
{
  if i < |s| then s[i] else 0.0
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
/* code modified by LLM (iteration 2): Changed array to seq and fixed assignment syntax */
{
  var length := max(|c1|, |c2|);
  result := [];
  var i := 0;
  while i < length
    invariant 0 <= i <= length
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == GetValue(c1, j) + GetValue(c2, j)
  {
    result := result + [GetValue(c1, i) + GetValue(c2, i)];
    i := i + 1;
  }
}
// </vc-code>
