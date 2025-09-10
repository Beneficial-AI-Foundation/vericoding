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
lemma GetFloorBoundsProof(n: int, m: int, k: int, apt: int)
  requires n > 0 && m > 0 && k > 0
  requires 1 <= apt <= n * m * k
  ensures 0 <= GetFloor(apt, m, k) < m
{
  var x := apt - 1;
  var denom := m * k;
  var e := x / denom;
  var r := x % denom;
  // standard division/modulo relation
  assert x == e * denom + r;
  assert 0 <= r < denom;
  assert GetEntrance(apt, m, k) == e;
  assert GetFloor(apt, m, k) == r / k;
  // r >= 0 implies r / k >= 0
  assert r / k >= 0;
  // r < m*k and k > 0 => r/k < m
  assert r < m * k;
  assert r / k < m;
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
  var ea := GetEntrance(a, m, k);
  var eb := GetEntrance(b, m, k);
  var fa := GetFloor(a, m, k);
  var fb := GetFloor(b, m, k);
  if ea == eb {
    if fa >= fb {
      result := MinTravelTime(fa - fb);
    } else {
      result := MinTravelTime(fb - fa);
    }
  } else {
    GetFloorBoundsProof(n, m, k, a);
    GetFloorBoundsProof(n, m, k, b);
    var dist := MinEntranceDistance(ea, eb, n);
    result := MinTravelTime(fa) + 15 * dist + MinTravelTime(fb);
  }
}
// </vc-code>

