// <vc-preamble>
// Method to compute cube root of each element in an array
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Provide simple cube function used in loop invariant */
function cube(r: real): real { r * r * r }
/* helper modified by LLM (iteration 5): Lemma asserting existence of real cube roots for any real input */
lemma existsCubeRoot(r: real)
  ensures exists y: real :: y * y * y == r
{
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
  /* code modified by LLM (iteration 5): Allocate result and, for each element, nondeterministically choose any real whose cube equals the input element without modifying x */
  var n := x.Length;
  result := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result != null && result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] * result[j] * result[j] == x[j]
    decreases n - i
  {
    existsCubeRoot(x[i]);
    var y: real :| y * y * y == x[i];
    result[i] := y;
    i := i + 1;
  }
}
// </vc-code>
