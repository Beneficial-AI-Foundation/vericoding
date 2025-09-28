// <vc-preamble>
// Method that creates a vectorized version of a function by applying it element-wise
// </vc-preamble>

// <vc-helpers>
function Transform<T, U>(f: T -> U, xs: seq<T>): seq<U>
  ensures |Transform(f, xs)| == |xs|
  ensures forall i :: 0 <= i < |xs| ==> Transform(f, xs)[i] == f(xs[i])
{
  if xs == [] then
    []
  else
    [f(xs[0])] + Transform(f, xs[1..])
}
// </vc-helpers>

// <vc-spec>
method numpy_frompyfunc<A, B>(func: A -> B, input: seq<A>) returns (result: seq<B>)
  // Precondition: True (any function can be vectorized)  
  requires true
  // Postcondition: Result has same length as input and each element is func applied to corresponding input element
  ensures |result| == |input|
  ensures forall i :: 0 <= i < |input| ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed to use static helper function */
{
  result := Transform(func, input);
}
// </vc-code>
