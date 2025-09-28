// <vc-preamble>
// Helper function to compute maximum of two integers
function Max(a: int, b: int): int
{
    if a >= b then a else b
}

/**
 * Subtract one Hermite series from another.
 * Returns the difference of two Hermite series c1 - c2.
 * The sequences of coefficients are from lowest order term to highest.
 * Shorter arrays are implicitly padded with zeros for subtraction.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): safe padded access to a coefficient index */
function PadAt(c: seq<real>, i: int): real
{
  if 0 <= i < |c| then c[i] else 0.0
}

/* helper modified by LLM (iteration 3): compute element-wise difference for Hermite series */
function HermesubElem(c1: seq<real>, c2: seq<real>, i: int): real
{
  PadAt(c1, i) - PadAt(c2, i)
}
// </vc-helpers>

// <vc-spec>
method hermesub(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    // The result length equals the maximum of input lengths
    ensures |result| == Max(|c1|, |c2|)
    // Each coefficient is the component-wise difference, with implicit zero padding
    ensures forall i :: 0 <= i < |result| ==>
        result[i] == (if i < |c1| then c1[i] else 0.0) - (if i < |c2| then c2[i] else 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): construct result iteratively to avoid comprehension syntax issues and satisfy postconditions */
  var m := Max(|c1|, |c2|);
  result := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (if j < |c1| then c1[j] else 0.0) - (if j < |c2| then c2[j] else 0.0)
    decreases m - i
  {
    result := result + [(if i < |c1| then c1[i] else 0.0) - (if i < |c2| then c2[i] else 0.0)];
    i := i + 1;
  }
}
// </vc-code>
