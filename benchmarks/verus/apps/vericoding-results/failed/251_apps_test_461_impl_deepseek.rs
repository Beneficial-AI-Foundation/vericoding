// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int, c: int) -> bool {
    1 <= n <= 100 && 1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

spec fn min_distance(n: int, a: int, b: int, c: int) -> int
    recommends valid_input(n, a, b, c)
{
    if n == 1 { 0 } else { (n - 1) * min(a, b) }
}

spec fn min(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

spec fn max(x: int, y: int) -> int {
    if x >= y { x } else { y }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_min_properties(a: int, b: int) 
    requires a >= 0, b >= 0
    ensures min(a, b) <= a, min(a, b) <= b
    {
}

proof fn lemma_max_properties(a: int, b: int, c: int) 
    requires a >= 0, b >= 0, c >= 0
    ensures 
        max(a, max(b, c)) >= a, 
        max(a, max(b, c)) >= b, 
        max(a, max(b, c)) >= c,
        max(a, max(b, c)) == max(max(a, b), c)
    {
}

proof fn lemma_distance_properties(a: int, b: int, c: int) 
    requires 
        1 <= a <= 100,
        1 <= b <= 100,
        1 <= c <= 100
    ensures 
        min(a, b) <= max(a, max(b, c)),
        min(a, b) >= 1
    {
}

fn convert_to_i8(value: int) -> (result: i8)
    requires 0 <= value <= 127
    ensures result as int == value
{
    /* helper modified by LLM (iteration 5): Safe int to i8 conversion */
    if value <= 127 {
        value as i8
    } else {
        vstd::pervasive::unreached()
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(n as int, a as int, b as int, c as int)
    ensures 
        result >= 0,
        n == 1 ==> result == 0,
        result as int <= (n as int - 1) * max(a as int, max(b as int, c as int)),
        result as int == min_distance(n as int, a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion by using ghost variable for verification */
    if n == 1 {
        return 0;
    }
    
    let exec_result_val = if a < b { a } else { b };
    let exec_result_val = exec_result_val * (n - 1);
    
    proof {
        let n_int = n as int;
        let a_int = a as int;
        let b_int = b as int;
        let c_int = c as int;
        
        let min_ab = min(a_int, b_int);
        let computed_distance = min_ab * (n_int - 1);
        
        assert(exec_result_val as int == computed_distance);
        assert(computed_distance >= 0) by {
            assert(min_ab >= 1);
            assert(n_int - 1 >= 1);
        }
    }
    
    assert(exec_result_val >= 0);
    convert_to_i8(exec_result_val as int)
}
// </vc-code>


}

fn main() {}