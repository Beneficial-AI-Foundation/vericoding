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
lemma MinTravelTimeMonotonic(x: int, y: int)
  requires x >= 0 && y >= 0
  requires x <= y
  ensures MinTravelTime(x) <= MinTravelTime(y)
{
  if x == y {
  } else {
    var stair_time_x := 5 * x;
    var elevator_time_x := 10 + x;
    var stair_time_y := 5 * y;
    var elevator_time_y := 10 + y;
    
    assert stair_time_x <= stair_time_y;
    assert elevator_time_x <= elevator_time_y;
    
    if stair_time_x < elevator_time_x {
      if stair_time_y < elevator_time_y {
        // Both use stairs
        assert MinTravelTime(x) == stair_time_x;
        assert MinTravelTime(y) == stair_time_y;
      } else {
        // x uses stairs, y uses elevator
        assert MinTravelTime(x) == stair_time_x;
        assert MinTravelTime(y) == elevator_time_y;
        assert stair_time_x <= stair_time_y <= elevator_time_y;
      }
    } else {
      assert MinTravelTime(x) == elevator_time_x;
      if stair_time_y < elevator_time_y {
        assert MinTravelTime(y) == stair_time_y;
        assert elevator_time_x <= elevator_time_y;
        assert stair_time_y < elevator_time_y;
      } else {
        assert MinTravelTime(y) == elevator_time_y;
        assert elevator_time_x <= elevator_time_y;
      }
    }
  }
}

lemma AptBounds(apt: int, n: int, m: int, k: int)
  requires n > 0 && m > 0 && k > 0 && 1 <= apt <= n * m * k
  ensures 1 <= apt <= n * m * k
{
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
  
  if entrance_a == entrance_b {
    var floor_diff := if floor_a >= floor_b then floor_a - floor_b else floor_b - floor_a;
    result := MinTravelTime(floor_diff);
  } else {
    var entrance_dist := MinEntranceDistance(entrance_a, entrance_b, n);
    
    // Prove floor bounds to help monotonicity
    assert 0 <= floor_a < m by { FloorProperties(a, m, k); }
    assert 0 <= floor_b < m by { FloorProperties(b, m, k); }
    
    // Prove entrance bounds to help distance calculation
    assert 0 <= entrance_a < n by { EntranceProperties(a, m, k, n); }
    assert 0 <= entrance_b < n by { EntranceProperties(b, m, k, n); }
    
    // Prove entrance distance is non-negative and bounded
    assert entrance_dist >= 0 by { DistanceProperties(entrance_a, entrance_b, n); }
    assert entrance_dist <= n / 2 by { DistanceProperties(entrance_a, entrance_b, n); }
    
    result := MinTravelTime(floor_a) + 15 * entrance_dist + MinTravelTime(floor_b);
  }
}
// </vc-code>

