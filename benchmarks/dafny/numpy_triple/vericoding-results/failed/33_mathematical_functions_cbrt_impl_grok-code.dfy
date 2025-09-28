// <vc-preamble>
// Method to compute cube root of each element in an array
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): kept cube_root function as is, no modifications needed */
function cube_root(x: real): real{
  if x == 0.0 then 0.0
  else if x > 0.0 then x^(1.0/3.0)
  else -( (-x)^(1.0/3.0) )
}
// </vc-helpers>

// <vc-spec>
method cbrt(x: array<real>) returns (result: array<real>)
  // Postconditions: result array properties
  ensures result.Length == x.Length
  // Core specification: each result element is the cube root of corresponding input element
  ensures forall i :: 0 <= i < result.Length ==> 
    result[i] * result[i] * result[i] == x[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed for loop syntax to use correct Dafny for loop (i := 0 to x.Length-1) with proper braces */
  result := new real[x.Length];
  for i := 0 to x.Length - 1 {
    result[i] := cube_root(x[i]);
  }
}
// </vc-code>
