// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary helper functions as the iterative implementation can use the 'power' function from the specification directly in its invariant. */
// </vc-helpers>

// <vc-spec>
function power(a: int, n: int): int
  requires 0 <= a && 0 <= n;
  decreases n;{if (n == 0) then 1 else a * power(a, n - 1)}

method compute_power(a: int, n: int) returns (s: int)
  requires n >= 0 && a >= 0;
  ensures s == power(a,n);
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Implemented a standard iterative solution using a while loop. */
  s := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == power(a, i)
    decreases n - i
  {
    s := s * a;
    i := i + 1;
  }
}
// </vc-code>
