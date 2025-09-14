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
lemma FloorNonNeg(apt: int, m: int, k: int)
  requires apt >= 1 && m > 0 && k > 0
  ensures GetFloor(apt, m, k) >= 0
{
  var e := GetEntrance(apt, m, k);
  var d := m * k;
  assert d > 0;
  assert (apt - 1) % d == (apt - 1) - d * ((apt - 1) / d);
  var r := (apt - 1) - e * d;
  assert e == (apt - 1) / d;
  assert r == (apt - 1) - d * ((apt - 1) / d);
  assert r == (apt - 1) % d;
  assert 0 <= r;
  assert GetFloor(apt, m, k) == r / k;
  assert k > 0;
  assert r / k >= 0;
}

lemma MinTravelTimeNonNeg(floors: int)
  requires floors >= 0
  ensures MinTravelTime(floors) >= 0
{
  assert MinTravelTime(floors) == (if 5 * floors < 10 + floors then 5 * floors else 10 + floors);
  assert 5 * floors >= 0;
  assert 10 + floors >= 0;
  if 5 * floors < 10 + floors {
  } else {
  }
}

lemma MinEntranceDistanceNonNeg(entrance_a: int, entrance_b: int, n: int)
  requires n > 0
  ensures MinEntranceDistance(entrance_a, entrance_b, n) >= 0
{
  var cw := (entrance_b - entrance_a + n) % n;
  var ccw := (entrance_a - entrance_b + n) % n;
  assert 0 <= cw;
  assert 0 <= ccw;
  assert MinEntranceDistance(entrance_a, entrance_b, n) == (if cw <= ccw then cw else ccw);
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
  var eA := GetEntrance(a, m, k);
  var eB := GetEntrance(b, m, k);
  var fA := GetFloor(a, m, k);
  var fB := GetFloor(b, m, k);

  if eA == eB {
    var diff := if fA >= fB then fA - fB else fB - fA;
    assert diff >= 0;
    MinTravelTimeNonNeg(diff);
    result := MinTravelTime(diff);
  } else {
    FloorNonNeg(a, m, k);
    FloorNonNeg(b, m, k);
    MinTravelTimeNonNeg(fA);
    MinTravelTimeNonNeg(fB);
    MinEntranceDistanceNonNeg(eA, eB, n);
    result := MinTravelTime(fA) + 15 * MinEntranceDistance(eA, eB, n) + MinTravelTime(fB);
  }
}
// </vc-code>

