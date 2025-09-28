// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int, y: int) -> bool {
    x != 0 && y != 0
}

spec fn valid_output(result: Seq<int>, x: int, y: int) -> bool {
    result.len() == 4 &&
    result[0] < result[2] &&
    (x * y > 0 && x < 0 ==> result =~= seq![x + y, 0, 0, x + y]) &&
    (x * y > 0 && x >= 0 ==> result =~= seq![0, x + y, x + y, 0]) &&
    (x * y <= 0 && x < 0 ==> result =~= seq![x - y, 0, 0, y - x]) &&
    (x * y <= 0 && x >= 0 ==> result =~= seq![0, y - x, x - y, 0])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(x: i8, y: i8) -> (result: Vec<i8>)
    requires valid_input(x as int, y as int)
    ensures valid_output(result@.map(|i: int, v: i8| v as int), x as int, y as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Used executable i8 arithmetic instead of ghost int casts to avoid compilation errors */
    let xy = x * y;
    let sum = x + y;
    let diff_xy = x - y;
    let diff_yx = y - x;
    let mut result: Vec<i8> = Vec::new();
    if xy > 0 && x < 0 {
        result.push(sum);
        result.push(0);
        result.push(0);
        result.push(sum);
    } else if xy > 0 && x >= 0 {
        result.push(0);
        result.push(sum);
        result.push(sum);
        result.push(0);
    } else if xy <= 0 && x < 0 {
        result.push(diff_xy);
        result.push(0);
        result.push(0);
        result.push(diff_yx);
    } else {
        result.push(0);
        result.push(diff_yx);
        result.push(diff_xy);
        result.push(0);
    }
    result
}
// </vc-code>


}

fn main() {}