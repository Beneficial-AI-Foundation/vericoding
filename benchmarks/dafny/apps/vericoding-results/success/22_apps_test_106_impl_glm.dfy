predicate ValidInput(n: int, m: int, k: int, a: int, b: int) {
  n > 0 && m > 0 && k > 0 && 1 <= a <= n * m * k && 1 <= b <= n * m * k && a != b
}

function GetEntrance(apt: int, m: int, k: int): int
  requires apt >= 1
  requires m > 0 && k > 0
{
  (apt - 1) / (m * k)
}

function GetFloor(apt: int, m: int, k: int): int
  requires apt >= 1
  requires m > 0 && k > 0
{
  ((apt - 1) - GetEntrance(apt, m, k) * m * k) / k
}

function MinTravelTime(floors: int): int
  requires floors >= 0
{
  var stair_time := 5 * floors;
  var elevator_time := 10 + floors;
  if stair_time < elevator_time then stair_time else elevator_time
}

function MinEntranceDistance(entrance_a: int, entrance_b: int, n: int): int
  requires n > 0
{
  var clockwise := (entrance_b - entrance_a + n) % n;
  var counterclockwise := (entrance_a - entrance_b + n) % n;
  if clockwise <= counterclockwise then clockwise else counterclockwise
}

// <vc-helpers>
lemma GetEntrance_Within_Bounds(apt: int, m: int, k: int, n: int)
  requires apt >= 1
  requires m > 0 && k > 0
  requires n > 0
  requires apt <= n * m * k
  ensures 0 <= GetEntrance(apt, m, k) < n
{
  var base := apt - 1;
  assert base >= 0 && base < n * m * k;
  assert base / (m*k) < n;
  assert GetEntrance(apt, m, k) == base / (m*k);
}

lemma GetFloor_Within_Bounds(apt: int, m: int, k: int)
  requires apt >= 1
  requires m > 0 && k > 0
  ensures 0 <= GetFloor(apt, m, k) < m
{
  var base := apt - 1;
  var entrance := base / (m*k);
  var remainder := base - entrance * (m*k);
  assert remainder >= 0 && remainder < m*k;
  assert 0 <= remainder / k < m;
  assert GetFloor(apt, m, k) == remainder / k;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int, a: int, b: int) returns (result: int)
  requires ValidInput(n, m, k, a, b)
  ensures result >= 0
  ensures GetEntrance(a, m, k) == GetEntrance(b, m, k) ==> 
    result == MinTravelTime(if GetFloor(a, m, k) >= GetFloor(b, m, k) 
                           then GetFloor(a, m, k) - GetFloor(b, m, k) 
                           else GetFloor(b, m, k) - GetFloor(a, m, k))
  ensures GetEntrance(a, m, k) != GetEntrance(b, m, k) ==>
    result == MinTravelTime(GetFloor(a, m, k)) + 
              15 * MinEntranceDistance(GetEntrance(a, m, k), GetEntrance(b, m, k), n) + 
              MinTravelTime(GetFloor(b, m, k))
// </vc-spec>
// <vc-code>
{
  GetEntrance_Within_Bounds(a, m, k, n);
  GetEntrance_Within_Bounds(b, m, k, n);
  GetFloor_Within_Bounds(a, m, k);
  GetFloor_Within_Bounds(b, m, k);

  var entrance_a := GetEntrance(a, m, k);
  var entrance_b := GetEntrance(b, m, k);
  var floor_a := GetFloor(a, m, k);
  var floor_b := GetFloor(b, m, k);
  if entrance_a == entrance_b {
      result := MinTravelTime(if floor_a >= floor_b then floor_a - floor_b else floor_b - floor_a);
  } else {
      result := MinTravelTime(floor_a) + 
                15 * MinEntranceDistance(entrance_a, entrance_b, n) + 
                MinTravelTime(floor_b);
  }
}
// </vc-code>

