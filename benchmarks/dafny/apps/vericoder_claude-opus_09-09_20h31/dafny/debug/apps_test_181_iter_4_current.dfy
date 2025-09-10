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
lemma DeviationProperties()
    ensures forall angle :: 0 <= angle < 360 ==> 0 <= DeviationFromVertical(angle) <= 180
    ensures forall angle :: 0 <= angle < 360 ==> DeviationFromVertical(angle) == 0 <==> angle == 0
{
    forall angle | 0 <= angle < 360
        ensures 0 <= DeviationFromVertical(angle) <= 180
        ensures DeviationFromVertical(angle) == 0 <==> angle == 0
    {
        if angle == 0 {
            assert DeviationFromVertical(angle) == 0;
        } else if 0 < angle <= 180 {
            assert DeviationFromVertical(angle) == angle;
            assert angle > 0;
            assert DeviationFromVertical(angle) > 0;
        } else {
            assert 180 < angle < 360;
            assert DeviationFromVertical(angle) == 360 - angle;
            assert 0 < 360 - angle < 180;
            assert DeviationFromVertical(angle) > 0;
        }
    }
}

lemma NormalizeAngleProperties(angle: int)
    ensures 0 <= NormalizeAngle(angle) < 360
    ensures NormalizeAngle(angle) == angle % 360 || NormalizeAngle(angle) == angle % 360 + 360
{
    var n := angle % 360;
    if n < 0 {
        assert NormalizeAngle(angle) == n + 360;
        assert 0 <= n + 360 < 360;
    } else {
        assert NormalizeAngle(angle) == n;
        assert 0 <= n < 360;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
    ensures 0 <= result <= 3
    ensures IsOptimalRotations(x, result)
// </vc-spec>
// <vc-code>
{
    var dev0 := ImageDeviationAfterRotations(x, 0);
    var dev1 := ImageDeviationAfterRotations(x, 1);
    var dev2 := ImageDeviationAfterRotations(x, 2);
    var dev3 := ImageDeviationAfterRotations(x, 3);
    
    result := 0;
    var minDev := dev0;
    
    if dev1 < minDev || (dev1 == minDev && 1 <= result) {
        result := 1;
        minDev := dev1;
    }
    
    if dev2 < minDev || (dev2 == minDev && 2 <= result) {
        result := 2;
        minDev := dev2;
    }
    
    if dev3 < minDev || (dev3 == minDev && 3 <= result) {
        result := 3;
        minDev := dev3;
    }
    
    assert minDev == ImageDeviationAfterRotations(x, result);
    
    forall k | 0 <= k <= 3
        ensures ImageDeviationAfterRotations(x, result) < ImageDeviationAfterRotations(x, k) || 
                (ImageDeviationAfterRotations(x, result) == ImageDeviationAfterRotations(x, k) && result <= k)
    {
        if k == 0 {
            assert dev0 == ImageDeviationAfterRotations(x, 0);
        } else if k == 1 {
            assert dev1 == ImageDeviationAfterRotations(x, 1);
        } else if k == 2 {
            assert dev2 == ImageDeviationAfterRotations(x, 2);
        } else {
            assert k == 3;
            assert dev3 == ImageDeviationAfterRotations(x, 3);
        }
    }
}
// </vc-code>

