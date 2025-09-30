// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_solution(n: int, a: int, b: int, c: int) -> bool {
        a >= 0 && b >= 0 && c >= 0 && 3 * a + 5 * b + 7 * c == n
    }
    
    spec fn valid_result(n: int, result: Seq<int>) -> bool {
        (result.len() == 1 && result[0] == -1) ||
        (result.len() == 3 && result[0] >= 0 && result[1] >= 0 && result[2] >= 0 && 
         valid_solution(n, result[0], result[1], result[2]))
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fits_i8 predicate to check int fits in i8 */
spec fn fits_i8(x: int) -> bool {
    -128 <= x && x <= 127
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<i8>)
    requires 
        n as int >= 1,
    ensures 
        valid_result(n as int, result@.map(|_index, x: i8| x as int)),
        (n as int) % 3 == 0 ==> (result@.len() == 3 && result@.map(|_index, x: i8| x as int) == seq![(n as int) / 3, 0, 0]),
        (n as int) % 3 == 1 && (n as int) < 7 ==> (result@.len() == 1 && result@[0] as int == -1),
        (n as int) % 3 == 1 && (n as int) >= 7 ==> (result@.len() == 3 && result@.map(|_index, x: i8| x as int) == seq![((n as int) - 7) / 3, 0, 1]),
        (n as int) % 3 == 2 && (n as int) < 5 ==> (result@.len() == 1 && result@[0] as int == -1),
        (n as int) % 3 == 2 && (n as int) >= 5 ==> (result@.len() == 3 && result@.map(|_index, x: i8| x as int) == seq![((n as int) - 5) / 3, 1, 0])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement solve using i8 arithmetic to avoid ghost 'int' */
    let r: i8 = n % 3;
    if r == 0_i8 {
        let a: i8 = n / 3;
        proof {
            let ai: int = a as int;
            assert(ai >= 0);
        }
        let mut v = Vec::new();
        v.push(a);
        v.push(0_i8);
        v.push(0_i8);
        v
    } else if r == 1_i8 {
        if n < 7_i8 {
            let mut v = Vec::new();
            v.push(-1_i8);
            v
        } else {
            let a: i8 = (n - 7_i8) / 3;
            proof {
                let ai: int = a as int;
                assert(ai >= 0);
            }
            let mut v = Vec::new();
            v.push(a);
            v.push(0_i8);
            v.push(1_i8);
            v
        }
    } else {
        if n < 5_i8 {
            let mut v = Vec::new();
            v.push(-1_i8);
            v
        } else {
            let a: i8 = (n - 5_i8) / 3;
            proof {
                let ai: int = a as int;
                assert(ai >= 0);
            }
            let mut v = Vec::new();
            v.push(a);
            v.push(1_i8);
            v.push(0_i8);
            v
        }
    }
}
// </vc-code>

}

fn main() {}