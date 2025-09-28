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

    /* helper modified by LLM (iteration 3): Remove duplicate spec functions and update proof lemmas */
    proof fn check_divisible_by_3_lemma(n: int)
        requires
            n >= 0,
            n % 3 == 0,
        ensures
            valid_solution(n, n / 3, 0, 0)
    {
        assert(3 * (n / 3) + 5 * 0 + 7 * 0 == n);
    }

    proof fn check_mod1_small_case(n: int) 
        requires
            n >= 1,
            n % 3 == 1,
            n < 7,
        ensures
            forall|result: Seq<int>| !(result.len() == 3 && valid_solution(n, result[0], result[1], result[2]))
    {
        assert(n >= 1 && n % 3 == 1 && n < 7);
        assert(n == 1 || n == 4);
        assert(!valid_solution(n, 0, 0, 0));
        assert(!valid_solution(n, 0, 0, 1));
        assert(!valid_solution(n, 0, 1, 0));
        assert(!valid_solution(n, 1, 0, 0));
    }

    proof fn check_mod1_large_case(n: int) 
        requires
            n >= 7,
            n % 3 == 1,
        ensures
            valid_solution(n, (n - 7) / 3, 0, 1)
    {
        assert((n - 7) % 3 == 0);
        let a = (n - 7) / 3;
        assert(3 * a + 5 * 0 + 7 * 1 == n);
    }

    proof fn check_mod2_small_case(n: int) 
        requires
            n >= 1,
            n % 3 == 2,
            n < 5,
        ensures
            forall|result: Seq<int>| !(result.len() == 3 && valid_solution(n, result[0], result[1], result[2]))
    {
        assert(n >= 1 && n % 3 == 2 && n < 5);
        assert(n == 2);
        assert(!valid_solution(n, 0, 0, 0));
        assert(!valid_solution(n, 0, 0, 1));
        assert(!valid_solution(n, 0, 1, 0));
        assert(!valid_solution(n, 1, 0, 0));
    }

    proof fn check_mod2_large_case(n: int) 
        requires
            n >= 5,
            n % 3 == 2,
        ensures
            valid_solution(n, (n - 5) / 3, 1, 0)
    {
        assert((n - 5) % 3 == 0);
        let a = (n - 5) / 3;
        assert(3 * a + 5 * 1 + 7 * 0 == n);
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
    /* code modified by LLM (iteration 3): Proper implementation with necessary proofs */
    let n_int = n as i32;
    
    if n_int % 3 == 0 {
        proof {
            check_divisible_by_3_lemma(n_int as int);
        }
        let a = (n_int / 3) as i8;
        vec![a, 0, 0]
    } else if n_int % 3 == 1 {
        if n_int < 7 {
            proof {
                check_mod1_small_case(n_int as int);
            }
            vec![-1]
        } else {
            proof {
                check_mod1_large_case(n_int as int);
            }
            let a = ((n_int - 7) / 3) as i8;
            vec![a, 0, 1]
        }
    } else {
        if n_int < 5 {
            proof {
                check_mod2_small_case(n_int as int);
            }
            vec![-1]
        } else {
            proof {
                check_mod2_large_case(n_int as int);
            }
            let a = ((n_int - 5) / 3) as i8;
            vec![a, 1, 0]
        }
    }
}
// </vc-code>

}

fn main() {}