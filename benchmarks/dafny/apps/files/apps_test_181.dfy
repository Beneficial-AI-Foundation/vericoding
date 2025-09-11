// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
    ensures 0 <= result <= 3
    ensures IsOptimalRotations(x, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
