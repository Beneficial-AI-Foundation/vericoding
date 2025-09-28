// <vc-preamble>
// Method that concatenates two sequences along the first axis
// Equivalent to numpy.r_[array1, array2] which concatenates array1 and array2
// </vc-preamble>

// <vc-helpers>
function sconcat(a: seq<real>, b: seq<real>): seq<real>
  ensures |sconcat(a, b)| == |a| + |b|
  ensures forall i :: 0 <= i < |a| ==> sconcat(a, b)[i] == a[i]
  ensures forall j :: 0 <= j < |b| ==> sconcat(a, b)[|a| + j] == b[j]
{
  if |a| == 0 then
    b
  else
    [a[0]] + sconcat(a[1..], b)
}
// </vc-helpers>

// <vc-spec>
method r_(a: seq<real>, b: seq<real>) returns (result: seq<real>)
  // No preconditions - concatenation works for any two sequences
  // Postcondition: result length equals sum of input lengths
  ensures |result| == |a| + |b|
  // Postcondition: first |a| elements of result match elements of a (preserving order)
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i]
  // Postcondition: next |b| elements of result match elements of b (preserving order)
  ensures forall j :: 0 <= j < |b| ==> result[|a| + j] == b[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Use built-in sequence concatenation */
  result := a + b;
}
// </vc-code>
