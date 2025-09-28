// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == a * b
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [changed to iterative implementation to fix termination] */
  result := 0;
  var i := 0;
  if b >= 0 {
    while i < b
      invariant 0 <= i <= b
      invariant result == a * i
      decreases b - i
    {
      result := result + a;
      i := i + 1;
    }
  } else {
    var nb := -b;
    while i < nb
      invariant 0 <= i <= nb
      invariant result == a * i
      decreases nb - i
    {
      result := result + a;
      i := i + 1;
    }
    result := -result;
  }
}
// </vc-code>
