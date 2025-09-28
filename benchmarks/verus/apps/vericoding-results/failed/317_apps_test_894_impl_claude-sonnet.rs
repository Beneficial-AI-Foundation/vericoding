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
/* helper modified by LLM (iteration 5): added overflow checks for i8 arithmetic */
fn safe_add(x: i8, y: i8) -> i8
    requires x as int + y as int <= 127 && x as int + y as int >= -128
{
    x + y
}

fn safe_sub(x: i8, y: i8) -> i8
    requires x as int - y as int <= 127 && x as int - y as int >= -128
{
    x - y
}

fn safe_mul_check(x: i8, y: i8) -> bool
    requires x != 0 && y != 0
{
    (x as int) * (y as int) <= 16384 && (x as int) * (y as int) >= -16384
}

spec fn compute_result_case1(x: int, y: int) -> Seq<int> {
    seq![x + y, 0, 0, x + y]
}

spec fn compute_result_case2(x: int, y: int) -> Seq<int> {
    seq![0, x + y, x + y, 0]
}

spec fn compute_result_case3(x: int, y: int) -> Seq<int> {
    seq![x - y, 0, 0, y - x]
}

spec fn compute_result_case4(x: int, y: int) -> Seq<int> {
    seq![0, y - x, x - y, 0]
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8, y: i8) -> (result: Vec<i8>)
    requires valid_input(x as int, y as int)
    ensures valid_output(result@.map(|i: int, v: i8| v as int), x as int, y as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added overflow checks before arithmetic operations */
    let mut result = Vec::new();
    
    let x_int = x as int;
    let y_int = y as int;
    
    if safe_mul_check(x, y) && x_int * y_int > 0 {
        if x < 0 {
            let sum = safe_add(x, y);
            result.push(sum);
            result.push(0);
            result.push(0);
            result.push(sum);
        } else {
            let sum = safe_add(x, y);
            result.push(0);
            result.push(sum);
            result.push(sum);
            result.push(0);
        }
    } else {
        if x < 0 {
            let diff1 = safe_sub(x, y);
            let diff2 = safe_sub(y, x);
            result.push(diff1);
            result.push(0);
            result.push(0);
            result.push(diff2);
        } else {
            let diff1 = safe_sub(y, x);
            let diff2 = safe_sub(x, y);
            result.push(0);
            result.push(diff1);
            result.push(diff2);
            result.push(0);
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}