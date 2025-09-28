// <vc-preamble>
// Helper function to compute maximum of two integers
function Max(a: int, b: int): int
{
  if a >= b then a else b
}

/**
 * Subtract one polynomial from another.
 * Takes two polynomial coefficient sequences and returns their difference c1 - c2.
 * Coefficients are ordered from lowest degree term to highest degree term.
 * The result has length equal to the maximum of the input lengths.
 */
// </vc-preamble>

// <vc-helpers>
function SafeAt(s: seq<real>, i: int): real
  requires 0 <= i
{
  if i < |s| then s[i] else 0.0
}

lemma SafeAtSubLemma(c1: seq<real>, c2: seq<real>, i: int)
  requires 0 <= i
  ensures SafeAt(c1, i) - SafeAt(c2, i) == 
    if i < |c1| && i < |c2| then c1[i] - c2[i]
    else if i < |c1| && i >= |c2| then c1[i]
    else if i >= |c1| && i < |c2| then -c2[i]
    else 0.0
{
  // Lemma automatically proved by SafeAt definition
}
// </vc-helpers>

// <vc-spec>
method PolySub(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  // The result length is the maximum of the two input lengths
  ensures |result| == Max(|c1|, |c2|)
  
  // Each coefficient in the result follows the subtraction rules
  ensures forall i :: 0 <= i < |result| ==>
    if i < |c1| && i < |c2| then 
      // Both polynomials have this coefficient: subtract
      result[i] == c1[i] - c2[i]
    else if i < |c1| && i >= |c2| then 
      // Only c1 has this coefficient: keep c1's coefficient
      result[i] == c1[i]
    else if i >= |c1| && i < |c2| then 
      // Only c2 has this coefficient: negate c2's coefficient
      result[i] == -c2[i]
    else 
      // Neither has this coefficient (this case shouldn't occur given length constraint)
      result[i] == 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed invariants and postcondition using SafeAt */
  var length := Max(|c1|, |c2|);
  result := [];
  var i := 0;
  while i < length
    invariant 0 <= i <= length
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == SafeAt(c1, j) - SafeAt(c2, j)
  {
    var val := SafeAt(c1, i) - SafeAt(c2, i);
    result := result + [val];
    i := i + 1;
  }
}
// </vc-code>
