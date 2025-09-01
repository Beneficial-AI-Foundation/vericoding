

// <vc-helpers>
lemma SquareLemma(n: int)
  requires n >= 0
  ensures n * n == (if n == 0 then 0 else (n-1)*(n-1) + 2*n - 1)
{
  if n > 0 {
    calc {
      n * n;
      ==
      ((n-1) + 1) * ((n-1) + 1);
      ==
      (n-1)*(n-1) + 2*(n-1) + 1;
      ==
      (n-1)*(n-1) + 2*n - 2 + 1;
      ==
      (n-1)*(n-1) + 2*n - 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method car_race_collision(n: int) returns (cnt: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures cnt == n * n
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    cnt := 0;
  } else {
    var prev := car_race_collision(n - 1);
    SquareLemma(n);
    cnt := prev + 2 * n - 1;
  }
}
// </vc-code>

