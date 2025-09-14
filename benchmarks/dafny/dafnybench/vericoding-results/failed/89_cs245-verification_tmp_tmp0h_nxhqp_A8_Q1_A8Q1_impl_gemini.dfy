// <vc-preamble>
function power(a: int, n: int): int
  requires 0 <= n;
  decreases n;
  {
    if (n == 0) then 1 else a * power(a, n - 1)
  }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed the now-unnecessary helper lemma. */
// </vc-helpers>

// <vc-spec>
method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0
ensures z==power(x,y0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Changed the loop to count up instead of down. */
  z := 1;
  var i := 0;
  while (i < y0)
    invariant 0 <= i <= y0
    invariant z == power(x, i)
    decreases y0 - i
  {
    z := z * x;
    i := i + 1;
  }
}
// </vc-code>
