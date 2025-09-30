// <vc-preamble>
// Method that creates a vectorized version of a function by applying it element-wise
// </vc-preamble>

// <vc-helpers>

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
  result := [];
  var i := 0;
  while i < |input|
    invariant 0 <= i <= |input|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == func(input[j])
  {
    result := result + [func(input[i])];
    i := i + 1;
  }
}
// </vc-code>
