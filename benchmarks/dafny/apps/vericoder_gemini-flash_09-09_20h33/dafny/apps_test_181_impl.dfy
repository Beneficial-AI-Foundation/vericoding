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
function Abs(x: int): int
    ensures Abs(x) >= 0
    ensures (Abs(x) == x || Abs(x) == -x)
    ensures (x >= 0 ==> Abs(x) == x)
{
    if x < 0 then -x else x
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
    ensures 0 <= result <= 3
    ensures IsOptimalRotations(x, result)
// </vc-spec>
// <vc-code>
{
    var minDeviation := 361; // Larger than any possible deviation (max is 180)
    result := 0;

    for k := 0 to 3
        invariant 0 <= k <= 4
        invariant 0 <= result <= 3
        invariant (minDeviation == 361 && k == 0) || (0 <= minDeviation <= 180)
        invariant (k > 0 ==> minDeviation == ImageDeviationAfterRotations(x, result))
        invariant forall j :: 0 <= j < k ==> 
            (ImageDeviationAfterRotations(x, result) < ImageDeviationAfterRotations(x, j) || 
            (ImageDeviationAfterRotations(x, result) == ImageDeviationAfterRotations(x, j) && result <= j))
    {
        var currentDeviation := ImageDeviationAfterRotations(x, k);
        if currentDeviation < minDeviation {
            minDeviation := currentDeviation;
            result := k;
        } else if currentDeviation == minDeviation {
            // According to IsOptimalRotations, if deviations are equal, choose the smaller k.
            // Since we iterate k from 0 upwards, if currentDeviation == minDeviation,
            // it means result (which is a previous k) is already smaller or equal.
            // So no change is needed for result, as result <= k holds.
        }
    }
}
// </vc-code>

