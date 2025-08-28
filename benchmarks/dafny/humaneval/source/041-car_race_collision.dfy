method car_race_collision(n: int) returns (cnt: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures cnt == n * n
  // post-conditions-end
{
  // impl-start
  cnt := n * n;
  // impl-end
}
