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
lemma MinTravelTime_nonneg(floors: int)
  requires floors >= 0
  ensures MinTravelTime(floors) >= 0
{
  assert 5 * floors >= 0;
  assert 10 + floors >= 0;
  if 5 * floors < 10 + floors {
    assert MinTravelTime(floors) == 5 * floors;
  } else {
    assert MinTravelTime(floors) == 10 + floors;
  }
}

lemma GetFloor_nonneg(apt: int, m: int, k: int)
  requires apt >= 1
  requires m > 0 && k > 0
  ensures GetFloor(apt, m, k) >= 0
{
  assert m * k > 0;
  var e := GetEntrance(apt, m, k);
  var r := (apt - 1) - e * m * k;
  assert e == (apt - 1) / (m * k);
  assert (apt - 1) == ((apt - 1) / (m * k)) * (m * k) + (apt - 1) % (m * k);
  calc {
    r;
    == { assert e == (apt - 1) / (m * k); }
       (apt - 1) - ((apt - 1) / (m * k)) * (m * k);
    == { assert (apt - 1) == ((apt - 1) / (m * k)) * (m * k) + (apt - 1) % (m * k); }
       ((apt - 1) / (m * k)) * (m * k) + (apt - 1) % (m * k) - ((apt - 1) / (m * k)) * (m * k);
    == (apt - 1) % (m * k);
  }
  assert 0 <= r;
  assert GetFloor(apt, m, k) == r / k;
  assert k > 0;
  assert r / k >= 0;
}

lemma MinEntranceDistance_nonneg(entrance_a: int, entrance_b: int, n: int)
  requires n > 0
  ensures MinEntranceDistance(entrance_a, entrance_b, n) >= 0
{
  assert 0 <= (entrance_b - entrance_a + n) % n;
  assert 0 <= (entrance_a - entrance_b + n) % n;
  if (entrance_b - entrance_a + n) % n <= (entrance_a - entrance_b + n) % n {
    assert MinEntranceDistance(entrance_a, entrance_b, n) == (entrance_b - entrance_a + n) % n;
  } else {
    assert MinEntranceDistance(entrance_a, entrance_b, n) == (entrance_a - entrance_b + n) % n;
  }
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
  if GetEntrance(a, m, k) == GetEntrance(b, m, k) {
    var fa := GetFloor(a, m, k);
    var fb := GetFloor(b, m, k);
    var d := if fa >= fb then fa - fb else fb - fa;
    if fa >= fb {
      assert d == fa - fb;
    } else {
      assert d == fb - fa;
    }
    assert d >= 0;
    MinTravelTime_nonneg(d);
    result := MinTravelTime(d);
  } else {
    var fa := GetFloor(a, m, k);
    var fb := GetFloor(b, m, k);
    GetFloor_nonneg(a, m, k);
    GetFloor_nonneg(b, m, k);
    MinTravelTime_nonneg(fa);
    MinEntranceDistance_nonneg(GetEntrance(a, m, k), GetEntrance(b, m, k), n);
    MinTravelTime_nonneg(fb);
    result := MinTravelTime(fa)
           + 15 * MinEntranceDistance(GetEntrance(a, m, k), GetEntrance(b, m, k), n)
           + MinTravelTime(fb);
  }
}
// </vc-code>

