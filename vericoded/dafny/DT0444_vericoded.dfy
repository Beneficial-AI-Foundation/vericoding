// <vc-preamble>
// Method to multiply two Hermite series represented as coefficient sequences
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added helper function for coefficient sum calculation */
function coeffSum(i: nat, j: nat, c1: seq<real>, c2: seq<real>): real
  requires i <= |c1|
  requires j <= |c2|
  decreases i
{
  if i == 0 then 0.0
  else if j >= i - 1 && i - 1 < |c1| && j - (i - 1) < |c2| then
    c1[i - 1] * c2[j - (i - 1)] + coeffSum(i - 1, j, c1, c2)
  else
    coeffSum(i - 1, j, c1, c2)
}
// </vc-helpers>

// <vc-spec>
method hermmul(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  ensures
    // Empty input handling: if either input is empty, return single zero coefficient
    (|c1| == 0 || |c2| == 0) ==> (|result| == 1 && result[0] == 0.0)
  ensures
    // Non-empty inputs have correct output size: m + n - 1 coefficients
    (|c1| > 0 && |c2| > 0) ==> |result| == |c1| + |c2| - 1
  ensures
    // Multiplication by constant polynomial (c2 has single coefficient)
    (|c2| == 1 && |c1| > 0) ==> 
      (|result| == |c1| && forall i :: 0 <= i < |c1| ==> result[i] == c1[i] * c2[0])
  ensures
    // Multiplication by constant polynomial (c1 has single coefficient)  
    (|c1| == 1 && |c2| > 0) ==> 
      (|result| == |c2| && forall i :: 0 <= i < |c2| ==> result[i] == c2[i] * c1[0])
  ensures
    // Zero polynomial property: if either input is all zeros, result is all zeros
    ((|c1| > 0 && forall i :: 0 <= i < |c1| ==> c1[i] == 0.0) ||
     (|c2| > 0 && forall j :: 0 <= j < |c2| ==> c2[j] == 0.0)) ==>
      (forall k :: 0 <= k < |result| ==> result[k] == 0.0)
  ensures
    // Result is never empty
    |result| >= 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Added proper handling and invariants for zero polynomial property */
  if |c1| == 0 || |c2| == 0 {
    result := [0.0];
  } else if |c1| == 1 {
    result := seq(|c2|, i requires 0 <= i < |c2| => c2[i] * c1[0]);
  } else if |c2| == 1 {
    result := seq(|c1|, i requires 0 <= i < |c1| => c1[i] * c2[0]);
  } else {
    var n := |c1| + |c2| - 1;
    result := seq(n, k => 0.0);
    
    var allZeros1 := forall i :: 0 <= i < |c1| ==> c1[i] == 0.0;
    var allZeros2 := forall j :: 0 <= j < |c2| ==> c2[j] == 0.0;
    
    if allZeros1 || allZeros2 {
      // Result is already initialized to all zeros
    } else {
      var i := 0;
      while i < |c1|
        invariant 0 <= i <= |c1|
        invariant |result| == n
        invariant n == |c1| + |c2| - 1
        invariant (allZeros1 || allZeros2) ==> (forall k :: 0 <= k < |result| ==> result[k] == 0.0)
      {
        var j := 0;
        while j < |c2|
          invariant 0 <= j <= |c2|
          invariant |result| == n
          invariant n == |c1| + |c2| - 1
          invariant i < |c1|
          invariant (allZeros1 || allZeros2) ==> (forall k :: 0 <= k < |result| ==> result[k] == 0.0)
        {
          if i + j < n {
            result := result[i + j := result[i + j] + c1[i] * c2[j]];
          }
          j := j + 1;
        }
        i := i + 1;
      }
    }
  }
}
// </vc-code>
