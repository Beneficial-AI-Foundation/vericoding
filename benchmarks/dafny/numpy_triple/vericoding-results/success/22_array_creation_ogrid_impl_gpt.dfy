// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added helpers to compute step and expected value for ogrid */
function stepBetween(start: real, stop: real, n: nat): real
  requires n > 1
{
  (stop - start) / ((n - 1) as real)
}

/* helper modified by LLM (iteration 2): added expectedVal to express the i-th value in the grid */
function expectedVal(start: real, stop: real, n: nat, i: nat): real
  requires n > 1
  requires i < n
{
  start + (i as real) * stepBetween(start, stop, n)
}
// </vc-helpers>

// <vc-spec>
method ogrid(start: real, stop: real, n: nat) returns (result: seq<real>)
  // Precondition: must have at least one point
  requires n > 0
  // Postcondition: result has exactly n elements
  ensures |result| == n
  // For single element case, it equals start
  ensures n == 1 ==> result[0] == start
  // For multiple elements, they are evenly spaced from start to stop
  ensures n > 1 ==> (forall i :: 0 <= i < n ==> 
    result[i] == start + (i as real) * ((stop - start) / ((n - 1) as real)))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build the sequence iteratively to avoid comprehension syntax issues and satisfy specs */
  if n == 1 {
    result := [start];
  } else {
    var step: real := (stop - start) / ((n - 1) as real);
    var r: seq<real> := [];
    var i: nat := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |r| == i
      invariant forall j :: 0 <= j < i ==> r[j] == start + (j as real) * step
    {
      r := r + [start + (i as real) * step];
      i := i + 1;
    }
    result := r;
  }
}
// </vc-code>
