function NormalizeAngle(angle: int): int
{
    var n := angle % 360;
    if n < 0 then n + 360 else n
}

function DeviationFromVertical(angle: int): int
    requires 0 <= angle < 360
{
    if angle <= 180 then angle else 360 - angle
}

function ImageAngleAfterRotations(cameraAngle: int, rotations: int): int
    requires 0 <= rotations <= 3
{
    NormalizeAngle(-cameraAngle + 90 * rotations)
}

function ImageDeviationAfterRotations(cameraAngle: int, rotations: int): int
    requires 0 <= rotations <= 3
{
    DeviationFromVertical(ImageAngleAfterRotations(cameraAngle, rotations))
}

predicate IsOptimalRotations(cameraAngle: int, result: int)
    requires 0 <= result <= 3
{
    forall k :: 0 <= k <= 3 ==> 
        var result_deviation := ImageDeviationAfterRotations(cameraAngle, result);
        var k_deviation := ImageDeviationAfterRotations(cameraAngle, k);
        result_deviation < k_deviation || (result_deviation == k_deviation && result <= k)
}

// <vc-helpers>
// <vc-helpers>
predicate OptimalAmongFirst(cameraAngle: int, upTo: int, cand: int, minDev: int)
  requires 0 <= upTo <= 3 && 0 <= cand <= upTo
{
  forall k :: 0 <= k <= upTo ==> 
    var result_deviation := ImageDeviationAfterRotations(cameraAngle, cand);
    var k_deviation := ImageDeviationAfterRotations(cameraAngle, k);
    result_deviation < k_deviation || (result_deviation == k_deviation && cand <= k)
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
    ensures 0 <= result <= 3
    ensures IsOptimalRotations(x, result)
// </vc-spec>
// <vc-code>
{
  var min_dev := 181;
  var candidate := 0;
  var dev0 := ImageDeviationAfterRotations(x, 0);
  min_dev := dev0;
  candidate := 0;
  var r := 1;
  while r <= 3
    invariant 1 <= r <= 4
    invariant candidate < r
    invariant min_dev == ImageDeviationAfterRotations(x, candidate)
    invariant OptimalAmongFirst(x, r-1, candidate, min_dev)
  {
    var dev := ImageDeviationAfterRotations(x, r);
    if dev < min_dev || (dev == min_dev && r < candidate)
    {
      min_dev := dev;
      candidate := r;
    }
    r := r + 1;
  }
  result := candidate;
}
// </vc-code>

