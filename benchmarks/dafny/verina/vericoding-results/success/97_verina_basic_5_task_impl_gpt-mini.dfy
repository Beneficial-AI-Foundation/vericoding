// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): termination measure for multiply_rec */
function multiply_rec(a: int, b: int): int
  decreases if b >= 0 then b else -b
{
  if b == 0 then 0
  else if b > 0 then a + multiply_rec(a, b - 1)
  else -multiply_rec(a, -b - 1) - a
}

/* helper modified by LLM (iteration 3): added decreases clause to enable recursion proof */
lemma MultiplyRecCorrect(a: int, b: int)
  ensures multiply_rec(a, b) == a * b
  decreases if b >= 0 then b else -b
{
  if b == 0 {
  } else if b > 0 {
    MultiplyRecCorrect(a, b - 1);
    assert multiply_rec(a, b) == a + multiply_rec(a, b - 1);
    assert multiply_rec(a, b) == a + a * (b - 1);
    assert multiply_rec(a, b) == a * b;
  } else {
    MultiplyRecCorrect(a, -b - 1);
    assert multiply_rec(a, b) == -multiply_rec(a, -b - 1) - a;
    assert multiply_rec(a, b) == -(a * (-b - 1)) - a;
    assert multiply_rec(a, b) == -(a * (-b - 1) + a);
    assert multiply_rec(a, b) == -(a * (-b - 1 + 1));
    assert multiply_rec(a, b) == a * b;
  }
}

// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == a * b
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): use multiply_rec and invoke proof lemma */
  result := multiply_rec(a, b);
  MultiplyRecCorrect(a, b);
}

// </vc-code>
