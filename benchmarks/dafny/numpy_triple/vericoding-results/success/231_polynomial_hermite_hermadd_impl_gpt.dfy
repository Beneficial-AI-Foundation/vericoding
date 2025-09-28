// <vc-preamble>
// Method to add two Hermite series represented as coefficient sequences
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): utility max function for integers */
function MaxInt(a: int, b: int): int
  ensures MaxInt(a, b) == (if a >= b then a else b)
{
  if a >= b then a else b
}
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
  /* code modified by LLM (iteration 2): build result via loop with invariants instead of invalid sequence comprehension */
  var n := if |c1| >= |c2| then |c1| else |c2|;
  var r: seq<real> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==>
      (if j < |c1| && j < |c2| then
         r[j] == c1[j] + c2[j]
       else if j < |c1| && j >= |c2| then
         r[j] == c1[j]
       else if j >= |c1| && j < |c2| then
         r[j] == c2[j]
       else
         r[j] == 0.0)
  {
    var v := if i < |c1| && i < |c2| then
                c1[i] + c2[i]
             else if i < |c1| && i >= |c2| then
                c1[i]
             else if i >= |c1| && i < |c2| then
                c2[i]
             else
                0.0;
    r := r + [v];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
