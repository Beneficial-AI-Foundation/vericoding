// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Sum(n: int): int
requires n >= 0
ensures Sum(n) == n * (n + 1) / 2
{
  if n == 0 then 0 else Sum(n - 1) + n
}
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)

  ensures r == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): Added conditional for negative n and used Sum function for positive n to ensure verifiable postcondition */
  if n < 0 {
    r := n * (n + 1) / 2;
  } else {
    r := Sum(n);
  }
}
// </vc-code>
