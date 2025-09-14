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
lemma NormalizeAngleRange(angle: int)
    ensures 0 <= NormalizeAngle(angle) < 360
{
}

lemma DeviationFromVerticalRange(angle: int)
    requires 0 <= angle < 360
    ensures 0 <= DeviationFromVertical(angle) <= 180
{
}

lemma ImageAngleAfterRotationsRange(cameraAngle: int, rotations: int)
    requires 0 <= rotations <= 3
    ensures 0 <= ImageAngleAfterRotations(cameraAngle, rotations) < 360
{
    NormalizeAngleRange(-cameraAngle + 90 * rotations);
}

lemma ImageDeviationAfterRotationsRange(cameraAngle: int, rotations: int)
    requires 0 <= rotations <= 3
    ensures 0 <= ImageDeviationAfterRotations(cameraAngle, rotations) <= 180
{
    ImageAngleAfterRotationsRange(cameraAngle, rotations);
    DeviationFromVerticalRange(ImageAngleAfterRotations(cameraAngle, rotations));
}

lemma OptimalRotationExists(cameraAngle: int)
    ensures exists r :: 0 <= r <= 3 && IsOptimalRotations(cameraAngle, r)
{
    var dev0 := ImageDeviationAfterRotations(cameraAngle, 0);
    var dev1 := ImageDeviationAfterRotations(cameraAngle, 1);
    var dev2 := ImageDeviationAfterRotations(cameraAngle, 2);
    var dev3 := ImageDeviationAfterRotations(cameraAngle, 3);
    
    if dev0 <= dev1 && dev0 <= dev2 && dev0 <= dev3 {
        assert IsOptimalRotations(cameraAngle, 0);
    } else if dev1 <= dev0 && dev1 <= dev2 && dev1 <= dev3 {
        assert IsOptimalRotations(cameraAngle, 1);
    } else if dev2 <= dev0 && dev2 <= dev1 && dev2 <= dev3 {
        assert IsOptimalRotations(cameraAngle, 2);
    } else {
        assert IsOptimalRotations(cameraAngle, 3);
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
    OptimalRotationExists(x);
    
    var dev0 := ImageDeviationAfterRotations(x, 0);
    var dev1 := ImageDeviationAfterRotations(x, 1);
    var dev2 := ImageDeviationAfterRotations(x, 2);
    var dev3 := ImageDeviationAfterRotations(x, 3);
    
    if dev0 < dev1 && dev0 < dev2 && dev0 < dev3 {
        result := 0;
    } else if dev1 < dev0 && dev1 < dev2 && dev1 < dev3 {
        result := 1;
    } else if dev2 < dev0 && dev2 < dev1 && dev2 < dev3 {
        result := 2;
    } else if dev3 < dev0 && dev3 < dev1 && dev3 < dev2 {
        result := 3;
    } else if dev0 <= dev1 && dev0 <= dev2 && dev0 <= dev3 {
        result := 0;
    } else if dev1 <= dev0 && dev1 <= dev2 && dev1 <= dev3 {
        result := 1;
    } else if dev2 <= dev0 && dev2 <= dev1 && dev2 <= dev3 {
        result := 2;
    } else {
        result := 3;
    }
}
// </vc-code>

