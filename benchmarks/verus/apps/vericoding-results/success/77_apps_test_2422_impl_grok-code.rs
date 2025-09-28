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
    /* code modified by LLM (iteration 2): fixed int type usage by using i32 for exec computations */
    proof {
        // We can use division by 3 as specified in the ensures clauses.
    }
    let n_val = n as i32;
    let rem = n_val % 3;
    if rem == 0 {
        let a = n_val / 3;
        let mut result = Vec::new();
        result.push(a as i8);
        result.push(0);
        result.push(0);
        result
    } else if rem == 1 {
        if n_val < 7 {
            let mut result = Vec::new();
            result.push(-1);
            result
        } else {
            let a = (n_val - 7) / 3;
            let mut result = Vec::new();
            result.push(a as i8);
            result.push(0);
            result.push(1);
            result
        }
    } else {  // rem == 2
        if n_val < 5 {
            let mut result = Vec::new();
            result.push(-1);
            result
        } else {
            let a = (n_val - 5) / 3;
            let mut result = Vec::new();
            result.push(a as i8);
            result.push(1);
            result.push(0);
            result
        }
    }
}
// </vc-code>

}

fn main() {}