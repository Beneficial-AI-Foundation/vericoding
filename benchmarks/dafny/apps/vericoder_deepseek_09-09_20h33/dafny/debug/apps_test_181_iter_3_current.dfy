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
lemma LemmaNormalizeAngleRange(angle: int)
    ensures 0 <= NormalizeAngle(angle) < 360
{
}

lemma LemmaDeviationFromVerticalRange(angle: int)
    requires 0 <= angle < 360
    ensures 0 <= DeviationFromVertical(angle) <= 180
{
}

lemma LemmaImageAngleAfterRotationsRange(cameraAngle: int, rotations: int)
    requires 0 <= rotations <= 3
    ensures 0 <= ImageAngleAfterRotations(cameraAngle, rotations) < 360
{
    LemmaNormalizeAngleRange(-cameraAngle + 90 * rotations);
}

lemma LemmaImageDeviationAfterRotationsRange(cameraAngle: int, rotations: int)
    requires 0 <= rotations <= 3
    ensures 0 <= ImageDeviationAfterRotations(cameraAngle, rotations) <= 180
{
    var angle := ImageAngleAfterRotations(cameraAngle, rotations);
    LemmaImageAngleAfterRotationsRange(cameraAngle, rotations);
    LemmaDeviationFromVerticalRange(angle);
}

lemma LemmaNormalizeAngleModulo(angle: int)
    ensures NormalizeAngle(angle) == angle % 360 + (if angle % 360 < 0 then 360 else 0)
{
}

lemma LemmaImageAngleAfterRotationsModulo(cameraAngle: int, rotations: int)
    requires 0 <= rotations <= 3
    ensures ImageAngleAfterRotations(cameraAngle, rotations) == (-cameraAngle + 90 * rotations) % 360 + (if (-cameraAngle + 90 * rotations) % 360 < 0 then 360 else 0)
{
    LemmaNormalizeAngleModulo(-cameraAngle + 90 * rotations);
}

lemma LemmaForallWeakening(rot: int, best_rot: int, x: int)
    requires 1 <= rot <= 4
    requires 0 <= best_rot <= 3
    requires forall k :: 0 <= k < rot - 1 ==> 
        var best_dev_val := ImageDeviationAfterRotations(x, best_rot);
        var k_dev := ImageDeviationAfterRotations(x, k);
        best_dev_val <= k_dev && (best_dev_val < k_dev || best_rot <= k)
    ensures forall k :: 0 <= k < rot - 1 ==> 
        var best_dev_val := ImageDeviationAfterRotations(x, best_rot);
        var k_dev := ImageDeviationAfterRotations(x, k);
        best_dev_val <= k_dev && (best_dev_val < k_dev || best_rot <= k)
{
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
    ensures 0 <= result <= 3
    ensures IsOptimalRotations(x, result)
// </vc-spec>
// <vc-code>
{
    var best_rot := 0;
    var best_dev := ImageDeviationAfterRotations(x, 0);
    LemmaImageDeviationAfterRotationsRange(x, 0);
    
    var rot := 1;
    while rot <= 3
        invariant 1 <= rot <= 4
        invariant 0 <= best_rot <= 3
        invariant forall k :: 0 <= k < rot ==> 
            var best_dev_val := ImageDeviationAfterRotations(x, best_rot);
            var k_dev := ImageDeviationAfterRotations(x, k);
            best_dev_val <= k_dev && (best_dev_val < k_dev || best_rot <= k)
    {
        LemmaImageDeviationAfterRotationsRange(x, rot);
        var current_dev := ImageDeviationAfterRotations(x, rot);
        if current_dev < best_dev || (current_dev == best_dev && rot < best_rot) {
            best_rot := rot;
            best_dev := current_dev;
        }
        LemmaForallWeakening(rot + 1, best_rot, x);
        rot := rot + 1;
    }
    
    result := best_rot;
}
// </vc-code>

