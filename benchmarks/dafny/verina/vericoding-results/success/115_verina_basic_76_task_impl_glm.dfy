// <vc-preamble>
// </vc-preamble>

// <vc-helpers>


// </vc-helpers>

// <vc-spec>
method MyMin(x: int, y: int) returns (result: int)
    ensures (x <= y ==> result == x) && (x > y ==> result == y)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed if-else syntax by using explicit blocks */
  if x <= y {
    result := x;
  } else {
    result := y;
  }
}
// </vc-code>
