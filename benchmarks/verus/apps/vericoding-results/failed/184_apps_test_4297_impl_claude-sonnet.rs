// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn divisible_by_both(result: int, n: int) -> bool
    recommends n >= 1
{
    result % 2 == 0 && result % n == 0
}

spec fn is_smallest(result: int, n: int) -> bool
    recommends n >= 1
{
    forall|k: int| 1 <= k < result ==> !(#[trigger] (k % 2) == 0 && #[trigger] (k % n) == 0)
}

spec fn lcm(a: int, b: int) -> int
    recommends a >= 1 && b >= 1
{
    if a % b == 0 {
        a
    } else if b % a == 0 {
        b
    } else {
        a * b
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type annotations and parameter types for compilation */
fn lemma_lcm_of_2_and_n(n: i8)
    requires n >= 1,
    ensures
        n as int % 2 == 0 ==> lcm(2int, n as int) == n as int,
        n as int % 2 != 0 ==> lcm(2int, n as int) == n as int * 2int,
{
    proof {
        if n as int % 2 == 0 {
            assert(n as int % 2 == 0);
        } else {
            assert(n as int % 2 != 0);
            assert(2int % n as int != 0);
        }
    }
}

fn lemma_result_is_smallest(n: int, result: int)
    requires
        n >= 1,
        result >= 1,
        result % 2 == 0 && result % n == 0,
        (n % 2 == 0 ==> result == n) && (n % 2 != 0 ==> result == n * 2),
    ensures
        forall|k: int| 1 <= k < result ==> !(#[trigger] (k % 2) == 0 && #[trigger] (k % n) == 0),
{
    proof {
        if n % 2 == 0 {
            assert(result == n);
            assert forall|k: int| 1 <= k < n implies !(k % 2 == 0 && k % n == 0) by {
                if 1 <= k < n {
                    if k % n == 0 {
                        assert(k >= n);
                        assert(false);
                    }
                }
            }
        } else {
            assert(result == n * 2int);
            assert forall|k: int| 1 <= k < n * 2int implies !(k % 2 == 0 && k % n == 0) by {
                if 1 <= k < n * 2int {
                    if k % 2 == 0 && k % n == 0 {
                        if k < n {
                            assert(k % n != 0);
                            assert(false);
                        } else {
                            assert(k >= n);
                            assert(k < n * 2int);
                            assert(k == n);
                            assert(n % 2 != 0);
                            assert(k % 2 != 0);
                            assert(false);
                        }
                    }
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        n >= 1,
    ensures 
        result >= 1,
        result as int % 2 == 0 && result as int % n as int == 0,
        forall|k: int| 1 <= k < result as int ==> !(#[trigger] (k % 2) == 0 && #[trigger] (k % n as int) == 0),
        (n as int % 2 == 0 ==> result as int == n as int) && (n as int % 2 != 0 ==> result as int == n as int * 2),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type casting for lemma call parameters */
    proof {
        if n as int % 2 == 0 {
            lemma_lcm_of_2_and_n(n);
            lemma_result_is_smallest(n as int, n as int);
        } else {
            let result = n * 2;
            lemma_lcm_of_2_and_n(n);
            lemma_result_is_smallest(n as int, result as int);
        }
    }
    
    if n % 2 == 0 {
        n
    } else {
        let result = n * 2;
        result
    }
}
// </vc-code>


}

fn main() {}