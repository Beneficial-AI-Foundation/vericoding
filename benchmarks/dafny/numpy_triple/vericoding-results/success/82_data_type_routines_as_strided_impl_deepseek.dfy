// <vc-preamble>
/*
 * Dafny specification for numpy.as_strided functionality.
 * Creates a view into an array with specified shape and strides,
 * accessing elements at regular stride intervals from the original array.
 */
// </vc-preamble>

// <vc-helpers>

function ComputeIndex(input_index: nat, stride: nat): nat { input_index * stride }

function ComputeStridedElement(x: seq<real>, index: nat, stride: nat): real
  requires index * stride < |x|
  requires stride > 0
{
  x[index * stride]
}

lemma StridedAccessValid(x: seq<real>, m: nat, stride: nat, i: nat)
  requires m * stride <= |x|
  requires stride > 0
  requires i < m
  ensures i * stride < |x|
  ensures i * stride <= |x| - stride
{
  /* helper modified by LLM (iteration 5): strengthened lemma with additional bound */
  assert i * stride <= (m-1) * stride by {
    if i < m {
      assert i <= m-1;
    }
  }
  assert (m-1) * stride < m * stride;
  assert m * stride <= |x|;
}


// </vc-helpers>

// <vc-spec>
method AsStrided(x: seq<real>, m: nat, stride: nat) returns (result: seq<real>)
  // Preconditions: Valid bounds and positive stride
  requires m * stride <= |x|
  requires stride > 0
  
  // Postconditions: Result has correct size and elements are strided from original
  ensures |result| == m
  ensures forall i :: 0 <= i < m ==> result[i] == x[i * stride]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed invariant with proper bounds */
  result := [];
  var i: nat := 0;
  
  while i < m
    invariant i <= m
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == x[j * stride]
  {
    StridedAccessValid(x, m, stride, i);
    result := result + [x[i * stride]];
    i := i + 1;
  }
}
// </vc-code>
