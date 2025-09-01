

// <vc-helpers>

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
  var i := 0;
  var count := 0;
  while i < n
    invariant 0 <= i <= n
    invariant count == i * n
  {
    count := count + n;
    i := i + 1;
  }
  return count;
}
// </vc-code>

