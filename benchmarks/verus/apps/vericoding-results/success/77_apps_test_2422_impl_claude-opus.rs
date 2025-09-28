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
    /* code modified by LLM (iteration 2): Fixed type conversion by working with i8 directly in executable code */
    
    if n % 3 == 0 {
        let a = n / 3;
        let mut result = Vec::new();
        result.push(a);
        result.push(0);
        result.push(0);
        
        proof {
            assert(3 * (n as int / 3) + 5 * 0 + 7 * 0 == n as int);
            assert(valid_solution(n as int, n as int / 3, 0, 0));
            assert(result@.map(|_index, x: i8| x as int) == seq![n as int / 3, 0, 0]);
        }
        
        result
    } else if n % 3 == 1 {
        if n < 7 {
            let mut result = Vec::new();
            result.push(-1);
            
            proof {
                assert(n as int == 1 || n as int == 4);
                assert(result@.len() == 1);
                assert(result@[0] as int == -1);
            }
            
            result
        } else {
            let a = (n - 7) / 3;
            let mut result = Vec::new();
            result.push(a);
            result.push(0);
            result.push(1);
            
            proof {
                assert((n as int - 7) % 3 == 0);
                assert(3 * ((n as int - 7) / 3) + 5 * 0 + 7 * 1 == n as int);
                assert(valid_solution(n as int, (n as int - 7) / 3, 0, 1));
                assert(result@.map(|_index, x: i8| x as int) == seq![(n as int - 7) / 3, 0, 1]);
            }
            
            result
        }
    } else {
        if n < 5 {
            let mut result = Vec::new();
            result.push(-1);
            
            proof {
                assert(n as int == 2);
                assert(result@.len() == 1);
                assert(result@[0] as int == -1);
            }
            
            result
        } else {
            let a = (n - 5) / 3;
            let mut result = Vec::new();
            result.push(a);
            result.push(1);
            result.push(0);
            
            proof {
                assert((n as int - 5) % 3 == 0);
                assert(3 * ((n as int - 5) / 3) + 5 * 1 + 7 * 0 == n as int);
                assert(valid_solution(n as int, (n as int - 5) / 3, 1, 0));
                assert(result@.map(|_index, x: i8| x as int) == seq![(n as int - 5) / 3, 1, 0]);
            }
            
            result
        }
    }
}
// </vc-code>

}

fn main() {}