// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function multRecursive(a: int, b: int): int
  decreases if b < 0 then -b else b
  ensures multRecursive(a, b) == a * b
{
  if b == 0 then
    0
  else if b > 0 then
    a + multRecursive(a, b - 1)
  else
    -a + multRecursive(a, b + 1)
}
// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == a * b
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): added verification with proper postcondition */
  result := multRecursive(a, b);
}
// </vc-code>
