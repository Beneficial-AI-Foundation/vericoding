// <vc-preamble>
// Method that creates a vectorized version of a function by applying it element-wise
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): identity function for generic type */
function id<A>(x: A): A { x }
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
{
  /* code modified by LLM (iteration 2): build result by iterative concatenation with invariants */
  var r: seq<B> := [];
  var i := 0;
  while i < |input|
    invariant 0 <= i <= |input|
    invariant |r| == i
    invariant forall j :: 0 <= j < |r| ==> r[j] == func(input[j])
  {
    r := r + [func(input[i])];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
