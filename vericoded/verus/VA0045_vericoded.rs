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
    /* code modified by LLM (iteration 2): Fixed type error by using i32 instead of int in executable code */
    let angle_i32: i32 = ((x as i32) % 360 + 360) % 360;
    
    let dev0: i32 = if angle_i32 <= 180 { angle_i32 } else { 360 - angle_i32 };
    let dev1: i32 = if angle_i32 <= 90 { 90 - angle_i32 } else if angle_i32 <= 270 { angle_i32 - 90 } else { 450 - angle_i32 };
    let dev2: i32 = if angle_i32 <= 180 { 180 - angle_i32 } else { angle_i32 - 180 };
    let dev3: i32 = if angle_i32 <= 90 { angle_i32 + 90 } else if angle_i32 <= 270 { 270 - angle_i32 } else { angle_i32 - 270 };
    
    let mut result = 0u8;
    let mut min_dev = dev0;
    
    if dev1 < min_dev {
        min_dev = dev1;
        result = 1;
    }
    
    if dev2 < min_dev {
        min_dev = dev2;
        result = 2;
    }
    
    if dev3 < min_dev {
        min_dev = dev3;
        result = 3;
    }
    
    result
}
// </vc-code>


}

fn main() {}