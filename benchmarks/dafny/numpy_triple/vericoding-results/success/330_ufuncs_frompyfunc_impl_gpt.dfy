// <vc-preamble>
// Method that creates a vectorized version of a function by applying it element-wise
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple sequence append helper to avoid comprehension syntax issues */
function appendOne<A>(s: seq<A>, x: A): seq<A>
  ensures appendOne(s, x) == s + [x]
  ensures |appendOne(s, x)| == |s| + 1
{
  s + [x]
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
{
  /* code modified by LLM (iteration 3): implement element-wise application via loop with invariants */
  var res: seq<B> := [];
  var i: int := 0;
  while i < |input|
    invariant 0 <= i <= |input|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == func(input[j])
    decreases |input| - i
  {
    res := res + [func(input[i])];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
