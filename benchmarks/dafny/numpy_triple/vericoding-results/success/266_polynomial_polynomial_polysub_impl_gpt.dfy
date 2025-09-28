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
/* helper modified by LLM (iteration 2): Safe coefficient accessor returning 0 outside bounds */
function GetCoeff(c: seq<real>, i: int): real
  requires 0 <= i
  ensures (i < |c|) ==> GetCoeff(c, i) == c[i]
  ensures (i >= |c|) ==> GetCoeff(c, i) == 0.0
{
  if i < |c| then c[i] else 0.0
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
  /* code modified by LLM (iteration 2): Construct result via loop to avoid comprehension parse issues and satisfy postconditions */
  var L := Max(|c1|, |c2|);
  var r: seq<real> := [];
  var i := 0;
  while i < L
    invariant 0 <= i <= L
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == GetCoeff(c1, j) - GetCoeff(c2, j)
    decreases L - i
  {
    r := r + [GetCoeff(c1, i) - GetCoeff(c2, i)];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
