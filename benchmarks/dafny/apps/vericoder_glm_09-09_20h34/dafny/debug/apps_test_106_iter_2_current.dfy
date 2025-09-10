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
lemma MinEntranceDistance_commutative(entrance_a: int, entrance_b: int, n: int)
  requires n > 0
  ensures MinEntranceDistance(entrance_a, entrance_b, n) == MinEntranceDistance(entrance_b, entrance_a, n)
{
  var clockwise1 := (entrance_b - entrance_a + n) % n;
  var counterclockwise1 := (entrance_a - entrance_b + n) % n;
  var clockwise2 := (entrance_a - entrance_b + n) % n;
  var counterclockwise2 := (entrance_b - entrance_a + n) % n;

  calc {
    MinEntranceDistance(entrance_a, entrance_b, n);
    if clockwise1 <= counterclockwise1 then clockwise1 else counterclockwise1;
    { assert clockwise1 == counterclockwise2; assert counterclockwise1 == clockwise2; }
    if counterclockwise2 <= clockwise2 then counterclockwise2 else clockwise2;
    MinEntranceDistance(entrance_b, entrance_a, n);
  }
}

lemma MinTravelTime_nonnegative(floors: int)
  requires floors >= 0
  ensures MinTravelTime(floors) >= 0
{
  var stair_time := 5 * floors;
  var elevator_time := 10 + floors;
  if stair_time < elevator_time {
    assert stair_time == MinTravelTime(floors);
    assert stair_time >= 0;
  } else {
    assert elevator_time == MinTravelTime(floors);
    assert elevator_time >= 0;
  }
}

lemma MinEntranceDistance_nonnegative(entrance_a: int, entrance_b: int, n: int)
  requires n > 0
  ensures MinEntranceDistance(entrance_a, entrance_b, n) >= 0
{
  var clockwise := (entrance_b - entrance_a + n) % n;
  var counterclockwise := (entrance_a - entrance_b + n) % n;
  var value := if clockwise <= counterclockwise then clockwise else counterclockwise;
  calc {
    MinEntranceDistance(entrance_a, entrance_b, n);
    value;
  }
  assert value >= 0;
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
    result := MinTravelTime(floor_a) + 
              15 * MinEntranceDistance(entrance_a, entrance_b, n) + 
              MinTravelTime(floor_b);
  }
}
// </vc-code>

