// <vc-preamble>
// Method to add two Legendre series by component-wise addition of coefficients
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple maximum of two ints */
function maxInt(a: int, b: int): int {
  if a >= b then a else b
}

/* helper modified by LLM (iteration 2): safe indexing with default 0.0 outside bounds */
function getWithDefault(s: seq<real>, i: int): real {
  if 0 <= i < |s| then s[i] else 0.0
}
// </vc-helpers>

// <vc-spec>
method LegendreAdd(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    // The result has length equal to the maximum of the input lengths
    ensures |result| == if |c1| >= |c2| then |c1| else |c2|
    // Each coefficient in the result is the sum of corresponding coefficients from inputs
    // Missing coefficients are treated as zero
    ensures forall i :: 0 <= i < |result| ==> 
        result[i] == (if i < |c1| then c1[i] else 0.0) + (if i < |c2| then c2[i] else 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterative construction of result sequence without comprehension; maintains invariants */
  var n := if |c1| >= |c2| then |c1| else |c2|;
  var res: seq<real> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == getWithDefault(c1, j) + getWithDefault(c2, j)
  {
    res := res + [getWithDefault(c1, i) + getWithDefault(c2, i)];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
