// <vc-preamble>
predicate ValidInput(d: int, k: int, a: int, b: int, t: int)
{
  d >= 1 && d <= 1000000000000 &&  // 10^12
  k >= 1 && k <= 1000000 &&        // 10^6
  a >= 1 && a <= 1000000 &&        // 10^6
  b >= 1 && b <= 1000000 &&        // 10^6
  t >= 1 && t <= 1000000 &&        // 10^6
  a < b
}

function min(x: int, y: int): int 
{ 
  if x <= y then x else y 
}

function WalkAllTheWay(d: int, b: int): int 
  requires d >= 1 && b >= 1
{ 
  d * b 
}

function DriveAllTheWay(d: int, k: int, a: int, t: int): int 
  requires d >= 1 && k >= 1 && a >= 1 && t >= 1
{ 
  d * a + (if d <= k then 0 else (d - 1) / k) * t 
}

function DriveKThenWalk(d: int, k: int, a: int, b: int): int 
  requires d >= 1 && k >= 1 && a >= 1 && b >= 1
{ 
  (if d <= k then d else k) * a + (if d <= k then 0 else d - k) * b 
}

function MixedStrategy(d: int, k: int, a: int, b: int, t: int): int 
  requires d >= 1 && k >= 1 && a >= 1 && b >= 1 && t >= 1
{
  var dd := d % k;
  var d1 := d - dd;
  var repairsNeeded := if d1 <= 0 then 0 else if d1 / k <= 1 then 0 else d1 / k - 1;
  d1 * a + repairsNeeded * t + dd * b
}

function OptimalTravelTime(d: int, k: int, a: int, b: int, t: int): int
  requires ValidInput(d, k, a, b, t)
  ensures OptimalTravelTime(d, k, a, b, t) >= 0
  ensures OptimalTravelTime(d, k, a, b, t) <= d * b
{
  min(min(min(WalkAllTheWay(d, b), DriveAllTheWay(d, k, a, t)), 
          DriveKThenWalk(d, k, a, b)), 
      MixedStrategy(d, k, a, b, t))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method calculateMinTravelTime(d: int, k: int, a: int, b: int, t: int) returns (minTime: int)
  requires ValidInput(d, k, a, b, t)
  ensures minTime >= 0
  ensures minTime <= d * b
  ensures minTime == OptimalTravelTime(d, k, a, b, t)
// </vc-spec>
// <vc-code>
{
  // Strategy 1: Walk all the way
  var t1 := d * b;

  // Strategy 2: Drive all the way with repairs
  var repairCount := if d <= k then 0 else (d - 1) / k;
  var t2 := d * a + repairCount * t;

  // Strategy 3: Drive up to k km, then walk the rest
  var driveDistance := if d <= k then d else k;
  var walkDistance := if d <= k then 0 else d - k;
  var t3 := driveDistance * a + walkDistance * b;

  // Strategy 4: Mixed strategy with optimal switching point
  var dd := d % k;
  var d1 := d - dd;
  var repairsNeeded := if d1 <= 0 then 0 else if d1 / k <= 1 then 0 else d1 / k - 1;
  var t4 := d1 * a + repairsNeeded * t + dd * b;

  // Return minimum of all strategies
  minTime := t1;
  if t2 < minTime { minTime := t2; }
  if t3 < minTime { minTime := t3; }
  if t4 < minTime { minTime := t4; }
}
// </vc-code>
