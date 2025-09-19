// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn normalize_angle(angle: int) -> int {
    let n = angle % 360;
    if n < 0 { n + 360 } else { n }
}

spec fn deviation_from_vertical(angle: int) -> int
    recommends 0 <= angle < 360
{
    if angle <= 180 { angle } else { 360 - angle }
}

spec fn image_angle_after_rotations(camera_angle: int, rotations: int) -> int
    recommends 0 <= rotations <= 3
{
    normalize_angle(-camera_angle + 90 * rotations)
}

spec fn image_deviation_after_rotations(camera_angle: int, rotations: int) -> int
    recommends 0 <= rotations <= 3
{
    deviation_from_vertical(image_angle_after_rotations(camera_angle, rotations))
}

spec fn is_optimal_rotations(camera_angle: int, result: int) -> bool
    recommends 0 <= result <= 3
{
    forall|k: int| 0 <= k <= 3 ==> #[trigger] image_deviation_after_rotations(camera_angle, k) >= image_deviation_after_rotations(camera_angle, result) && (image_deviation_after_rotations(camera_angle, k) > image_deviation_after_rotations(camera_angle, result) || result <= k)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: u8)
    ensures 
        0 <= result <= 3,
        is_optimal_rotations(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}