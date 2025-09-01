

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
cnt := n * n;
// </vc-code>

