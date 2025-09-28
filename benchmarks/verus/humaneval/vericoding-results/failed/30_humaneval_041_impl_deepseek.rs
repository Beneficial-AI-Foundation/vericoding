// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 0
}

spec fn collision_count(n: int) -> int
    recommends valid_input(n)
{
    n * n
}

spec fn valid_result(n: int, result: int) -> bool
    recommends valid_input(n)
{
    result == collision_count(n) && result >= 0
}
// </vc-preamble>

// <vc-helpers>


proof fn collision_count_formula_lemma(n: nat)
    ensures
        collision_count(n as int) == (n as int) * (n as int),
{
}

proof fn valid_result_lemma(n: nat, result: int)
    requires
        result == (n as int) * (n as int),
    ensures
        valid_result(n as int, result),
{
}

proof fn arithmetic_bounds_lemma(a: i8, b: i8)
    requires
        a >= 0,
        b >= 0,
        (a as int) * (b as int) <= 127,
    ensures
        a * b >= 0,
{
}

proof fn intermediate_result_lemma(i: i8, result: i8)
    requires
        i >= 0,
        (result as int) == (i as int) * (i as int),
        (result as int) + 2 * (i as int) + 1 <= 127,
    ensures
        (result + 2 * i + 1) as int == ((i + 1) as int) * ((i + 1) as int),
        result + 2 * i + 1 >= 0,
{
    assert((result + 2 * i + 1) as int == (result as int) + 2 * (i as int) + 1);
}

// </vc-helpers>

// <vc-spec>
fn car_race_collision(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add explicit cast to ensure arithmetic correctness */
    let mut result: i8 = 0;
    let mut i: i8 = 0;
    
    while i < n
        invariant
            i >= 0,
            i <= n,
            result >= 0,
            (result as int) == (i as int) * (i as int),
            (result as int) + 2 * (i as int) + 1 <= 127,
        decreases (n as int) - (i as int),
    {
        proof {
            intermediate_result_lemma(i, result);
        }
        
        result = (result as int + 2 * (i as int) + 1) as i8;
        i = i + 1;
    }
    
    proof {
        valid_result_lemma(n as nat, result as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}