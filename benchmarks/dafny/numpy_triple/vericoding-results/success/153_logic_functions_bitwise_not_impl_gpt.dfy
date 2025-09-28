// <vc-preamble>
/*
 * Dafny specification for numpy.bitwise_not operation.
 * Computes bit-wise inversion, or bit-wise NOT, element-wise on integer arrays.
 * In two's-complement representation, bitwise NOT of x equals -(x + 1).
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): pure function computing bitwise NOT as -(x + 1) */
function NotInt(x: int): int {
  -(x + 1)
}

/* helper modified by LLM (iteration 5): recursive function mapping NotInt over a sequence */
function MapNot(x: seq<int>): seq<int>
  decreases |x|
{
  if |x| == 0 then [] else [NotInt(x[0])] + MapNot(x[1..])
}

/* helper modified by LLM (iteration 5): lemma establishing MapNot length and element-wise property */
lemma Lemma_MapNotProps(x: seq<int>)
  ensures |MapNot(x)| == |x|
  ensures forall i :: 0 <= i < |x| ==> MapNot(x)[i] == NotInt(x[i])
  decreases |x|
{
  if |x| == 0 {
  } else {
    Lemma_MapNotProps(x[1..]);
    assert MapNot(x) == [NotInt(x[0])] + MapNot(x[1..]);
    assert |MapNot(x)| == 1 + |MapNot(x[1..])|;
    assert |x| == 1 + |x[1..]|;
    assert MapNot(x)[0] == NotInt(x[0]);
    forall i | 0 < i < |x|
      ensures MapNot(x)[i] == NotInt(x[i])
    {
      assert 0 <= i - 1;
      assert i - 1 < |x[1..]|;
      assert i - 1 < |MapNot(x[1..])|;
      assert (x[1..])[i - 1] == x[i];
      assert MapNot(x)[i] == MapNot(x[1..])[i - 1];
      assert MapNot(x[1..])[i - 1] == NotInt((x[1..])[i - 1]);
      assert NotInt((x[1..])[i - 1]) == NotInt(x[i]);
    }
  }
}

/* helper modified by LLM (iteration 5): predicate stating y is element-wise bitwise NOT of x */
predicate IsBitwiseNotOf(x: seq<int>, y: seq<int>) {
  |x| == |y| && (forall i :: 0 <= i < |x| ==> y[i] == NotInt(x[i]))
}
// </vc-helpers>

// <vc-spec>
method BitwiseNot(x: seq<int>) returns (result: seq<int>)
  // No special preconditions required for bitwise NOT operation
  requires true
  
  // Result has same length as input
  ensures |result| == |x|
  
  // Each element in result is the bitwise NOT of corresponding input element
  // In two's-complement: ~x = -(x + 1)
  ensures forall i :: 0 <= i < |x| ==> result[i] == -(x[i] + 1)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute result via recursive helper and use lemma for properties */
  Lemma_MapNotProps(x);
  result := MapNot(x);
}
// </vc-code>
