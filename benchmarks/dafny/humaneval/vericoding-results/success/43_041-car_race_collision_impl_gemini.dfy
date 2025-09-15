// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SquareSum(i: int) 
  ensures i * i + 2 * i + 1 == (i + 1) * (i + 1)
{
}
// </vc-helpers>

// <vc-spec>
method car_race_collision(n: int) returns (cnt: int)

  requires n >= 0

  ensures cnt == n * n
// </vc-spec>
// <vc-code>
{
  cnt := 0;
  var i := 0;
  while i < n 
    invariant 0 <= i <= n
    invariant cnt == i * i
  {
    cnt := cnt + (2 * i + 1);
    i := i + 1;
  }
}
// </vc-code>
