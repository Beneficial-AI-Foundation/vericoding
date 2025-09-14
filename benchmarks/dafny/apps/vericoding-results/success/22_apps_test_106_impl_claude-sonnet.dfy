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
lemma AbsoluteDifference(a: int, b: int)
  ensures a >= b ==> a - b >= 0
  ensures b > a ==> b - a >= 0
{
}

lemma EntranceProperties(apt: int, m: int, k: int)
  requires apt >= 1 && m > 0 && k > 0
  ensures GetEntrance(apt, m, k) >= 0
{
}

lemma FloorProperties(apt: int, m: int, k: int)
  requires apt >= 1 && m > 0 && k > 0
  ensures GetFloor(apt, m, k) >= 0
{
}

lemma MinTravelTimeNonNegative(floors: int)
  requires floors >= 0
  ensures MinTravelTime(floors) >= 0
{
}

lemma MinEntranceDistanceNonNegative(entrance_a: int, entrance_b: int, n: int)
  requires n > 0
  ensures MinEntranceDistance(entrance_a, entrance_b, n) >= 0
{
}

lemma EntranceBounds(apt: int, m: int, k: int, n: int)
  requires apt >= 1 && apt <= n * m * k && m > 0 && k > 0 && n > 0
  ensures 0 <= GetEntrance(apt, m, k) < n
{
  assert apt - 1 >= 0;
  assert apt - 1 < n * m * k;
  assert GetEntrance(apt, m, k) == (apt - 1) / (m * k);
  assert 0 <= (apt - 1) / (m * k) < n;
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
  EntranceProperties(a, m, k);
  EntranceProperties(b, m, k);
  FloorProperties(a, m, k);
  FloorProperties(b, m, k);
  
  var entrance_a := GetEntrance(a, m, k);
  var entrance_b := GetEntrance(b, m, k);
  var floor_a := GetFloor(a, m, k);
  var floor_b := GetFloor(b, m, k);
  
  if entrance_a == entrance_b {
    var floor_diff := if floor_a >= floor_b then floor_a - floor_b else floor_b - floor_a;
    AbsoluteDifference(floor_a, floor_b);
    MinTravelTimeNonNegative(floor_diff);
    result := MinTravelTime(floor_diff);
  } else {
    EntranceBounds(a, m, k, n);
    EntranceBounds(b, m, k, n);
    MinEntranceDistanceNonNegative(entrance_a, entrance_b, n);
    MinTravelTimeNonNegative(floor_a);
    MinTravelTimeNonNegative(floor_b);
    
    var time_to_ground_a := MinTravelTime(floor_a);
    var walking_time := 15 * MinEntranceDistance(entrance_a, entrance_b, n);
    var time_to_floor_b := MinTravelTime(floor_b);
    result := time_to_ground_a + walking_time + time_to_floor_b;
  }
}
// </vc-code>

