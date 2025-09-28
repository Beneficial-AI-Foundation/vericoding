// <vc-preamble>
// External logarithm function declaration
function {:extern} Log(x: real): real
  requires x > 0.0
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed redundant null check and proved positivity */
lemma ArrayPositivity(x: array<real>)
  requires forall i :: 0 <= i < x.Length ==> x[i] > 0.0
  ensures forall i :: 0 <= i < x.Length ==> x[i] > 0.0
{
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant forall j :: 0 <= j < i ==> x[j] > 0.0
  {
    assert x[i] > 0.0;
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method log(x: array<real>) returns (result: array<real>)
  // Precondition: All elements must be positive
  requires forall i :: 0 <= i < x.Length ==> x[i] > 0.0
  
  // Postcondition: Result has same length and each element is log of corresponding input element
  ensures result.Length == x.Length
  ensures forall i :: 0 <= i < result.Length ==> result[i] == Log(x[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): allocate result array and compute Log for each element */
  result := new real[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant result.Length == x.Length
    invariant forall j :: 0 <= j < i ==> result[j] == Log(x[j])
    invariant forall j :: 0 <= j < x.Length ==> x[j] > 0.0
  {
    result[i] := Log(x[i]);
    i := i + 1;
  }
}
// </vc-code>
