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

// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
    ensures 0 <= result <= 3
    ensures IsOptimalRotations(x, result)
// </vc-spec>
// <vc-code>
{
  var best := 0;
  var i := 1;
  while i <= 3
    invariant 1 <= i <= 4
    invariant 0 <= best <= i - 1
    invariant forall k :: 0 <= k < i ==>
      var bestD := ImageDeviationAfterRotations(x, best);
      var kD := ImageDeviationAfterRotations(x, k);
      bestD < kD || (bestD == kD && best <= k)
    decreases 4 - i
  {
    var bestD := ImageDeviationAfterRotations(x, best);
    var iD := ImageDeviationAfterRotations(x, i);
    if iD < bestD || (iD == bestD && i < best) {
      best := i;
    }
    i := i + 1;
  }
  assert i == 4;
  result := best;
}
// </vc-code>

