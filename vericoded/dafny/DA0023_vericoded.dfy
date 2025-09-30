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
lemma FloorDifferenceAbs(floor_a: int, floor_b: int)
  ensures floor_a >= floor_b ==> floor_a - floor_b >= 0
  ensures floor_b >= floor_a ==> floor_b - floor_a >= 0
  ensures (if floor_a >= floor_b then floor_a - floor_b else floor_b - floor_a) >= 0
{
  // This lemma helps Dafny understand the floor difference calculation
}

lemma MinTravelTimeNonNegative(floors: int)
  requires floors >= 0
  ensures MinTravelTime(floors) >= 0
{
  // This helps establish that MinTravelTime always returns non-negative values
}

lemma EntranceFloorBounds(apt: int, m: int, k: int)
  requires apt >= 1
  requires m > 0 && k > 0
  ensures GetEntrance(apt, m, k) >= 0
  ensures GetFloor(apt, m, k) >= 0
{
  // This helps establish that entrance and floor calculations are non-negative
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
  var entrance_a := GetEntrance(a, m, k);
  var entrance_b := GetEntrance(b, m, k);
  var floor_a := GetFloor(a, m, k);
  var floor_b := GetFloor(b, m, k);
  
  // Add assertions to help Dafny
  EntranceFloorBounds(a, m, k);
  EntranceFloorBounds(b, m, k);
  
  if entrance_a == entrance_b {
    // Same entrance - just travel between floors
    var floor_diff := if floor_a >= floor_b then floor_a - floor_b else floor_b - floor_a;
    FloorDifferenceAbs(floor_a, floor_b);
    assert floor_diff >= 0;
    result := MinTravelTime(floor_diff);
    MinTravelTimeNonNegative(floor_diff);
    assert result >= 0;
  } else {
    // Different entrances - travel to ground, between entrances, then up
    var time_down := MinTravelTime(floor_a);
    MinTravelTimeNonNegative(floor_a);
    assert time_down >= 0;
    
    var entrance_dist := MinEntranceDistance(entrance_a, entrance_b, n);
    assert entrance_dist >= 0;
    
    var time_between := 15 * entrance_dist;
    assert time_between >= 0;
    
    var time_up := MinTravelTime(floor_b);
    MinTravelTimeNonNegative(floor_b);
    assert time_up >= 0;
    
    result := time_down + time_between + time_up;
    assert result >= 0;
  }
}
// </vc-code>

