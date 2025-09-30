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
  var maxLen := if |c1| >= |c2| then |c1| else |c2|;
  result := [];
  var i := 0;
  while i < maxLen
    invariant 0 <= i <= maxLen
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      if j < |c1| && j < |c2| then
        result[j] == c1[j] + c2[j]
      else if j < |c1| && j >= |c2| then
        result[j] == c1[j]
      else if j >= |c1| && j < |c2| then
        result[j] == c2[j]
      else
        result[j] == 0.0
  {
    if i < |c1| && i < |c2| {
      result := result + [c1[i] + c2[i]];
    } else if i < |c1| && i >= |c2| {
      result := result + [c1[i]];
    } else if i >= |c1| && i < |c2| {
      result := result + [c2[i]];
    } else {
      result := result + [0.0];
    }
    i := i + 1;
  }
}
// </vc-code>
