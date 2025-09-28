// <vc-preamble>
// Method that horizontally stacks two 1D arrays (sequences) by concatenating them
// </vc-preamble>

// <vc-helpers>
function sliceAt<T>(s: seq<T>, start: int, end: int): seq<T>
  requires 0 <= start <= end <= |s|
  decreases end - start
{
  if start == end then []
  else [s[start]] + sliceAt(s, start + 1, end)
}

function concat<T>(s1: seq<T>, s2: seq<T>): seq<T>
  decreases |s1|
{
  if |s1| == 0 then s2
  else [s1[0]] + concat(s1[1..], s2)
}
// </vc-helpers>

// <vc-spec>
method hstack(a: seq<real>, b: seq<real>) returns (result: seq<real>)
  // No preconditions needed for 1D concatenation
  requires true
  
  // The result has length equal to the sum of input lengths
  ensures |result| == |a| + |b|
  
  // First |a| elements come from array a, preserving order
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i]
  
  // Next |b| elements come from array b, preserving order  
  ensures forall j :: 0 <= j < |b| ==> result[|a| + j] == b[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): add termination and fix concatenation */
  result := a + b;
}
// </vc-code>
