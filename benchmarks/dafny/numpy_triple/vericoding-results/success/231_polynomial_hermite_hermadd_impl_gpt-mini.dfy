// <vc-preamble>
// Method to add two Hermite series represented as coefficient sequences
// </vc-preamble>

// <vc-helpers>
function Max(a: int, b: int): int { if a >= b then a else b }
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
  var n1 := |c1|;
  var n2 := |c2|;
  var n := Max(n1, n2);
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==>
      if j < n1 && j < n2 then a[j] == c1[j] + c2[j]
      else if j < n1 then a[j] == c1[j]
      else if j < n2 then a[j] == c2[j]
      else a[j] == 0.0
  {
    if i < n1 && i < n2 {
      a[i] := c1[i] + c2[i];
    } else if i < n1 {
      a[i] := c1[i];
    } else if i < n2 {
      a[i] := c2[i];
    } else {
      a[i] := 0.0;
    }
    i := i + 1;
  }
  result := a[..];
}

// </vc-code>
