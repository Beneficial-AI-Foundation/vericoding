// <vc-preamble>
// Method to add two Hermite series represented as coefficient sequences
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method hermadd(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  // No preconditions needed for basic addition
  requires true
  
  // The result length is the maximum of the input lengths
  ensures |result| == if |c1| >= |c2| then |c1| else |c2|
  
  // Component-wise addition with implicit zero-padding for shorter sequences
  ensures forall i :: 0 <= i < |result| ==>
    if i < |c1| && i < |c2| then
      // Both sequences have coefficient at position i
      result[i] == c1[i] + c2[i]
    else if i < |c1| && i >= |c2| then
      // Only c1 has coefficient at position i (c2 treated as 0)
      result[i] == c1[i]
    else if i >= |c1| && i < |c2| then
      // Only c2 has coefficient at position i (c1 treated as 0)
      result[i] == c2[i]
    else
      // Neither sequence has coefficient at position i (both treated as 0)
      result[i] == 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Removed decreases clause to fix compilation error, as termination is inferred from loop condition and invariants. */
  var maxLen := if |c1| >= |c2| then |c1| else |c2|;
  var res: seq<real> := [];
  var i := 0;
  while i < maxLen
    invariant i <= maxLen
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==>
      res[k] == (if k < |c1| then c1[k] else 0.0) + (if k < |c2| then c2[k] else 0.0)
  {
    var val := 0.0;
    if i < |c1| { val := val + c1[i]; }
    if i < |c2| { val := val + c2[i]; }
    res := res + [val];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
