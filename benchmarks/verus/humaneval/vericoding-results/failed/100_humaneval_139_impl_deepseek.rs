// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial_func(num: int) -> int
    recommends num >= 0
    decreases num
{
    if num <= 1 { 1 } else { num * factorial_func(num - 1) }
}

spec fn special_factorial_func(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 { 1 }
    else { special_factorial_func(n - 1) * factorial_func(n) }
}

fn factorial(num: int) -> (result: int)
    requires 
        num >= 0,
    ensures 
        result == factorial_func(num),
        result > 0,
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_base_case()
    ensures special_factorial_func(0) == 1,
{
    assert(special_factorial_func(0) == 1);
}

proof fn lemma_inductive_step(n: int)
    requires
        n > 0,
        n > 0 ==> special_factorial_func(n - 1) * factorial_func(n) == special_factorial_func(n),
    ensures
        n > 0 ==> special_factorial_func(n - 1) * factorial_func(n) == special_factorial_func(n),
{
}

proof fn lemma_factorial_positive(n: int)
    requires
        n >= 0,
    ensures
        factorial_func(n) >= 1,
{
    if n > 0 {
        lemma_factorial_positive(n - 1);
    }
}

proof fn lemma_special_factorial_positive(n: int)
    requires
        n >= 0,
    ensures
        special_factorial_func(n) >= 1,
{
    if n > 0 {
        lemma_special_factorial_positive(n - 1);
        lemma_factorial_positive(n);
    }
}
// </vc-helpers>

// <vc-spec>
fn special_factorial(n: i8) -> (result: i8)
    requires 
        n >= 0,
    ensures 
        result as int == special_factorial_func(n as int),
        result > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors and added proper proof structure */
    if n == 0 {
        proof {
            lemma_base_case();
            lemma_special_factorial_positive(0);
        }
        assert(1 as int == special_factorial_func(0));
        assert(1 > 0);
        1
    } else {
        let k = n - 1;
        let prev = special_factorial(k);
        proof {
            assert(n as int > 0);
            assert(k as int >= 0);
        }
        let ghost n_int = n as int;
        let fact_result = factorial(n_int);
        proof {
            lemma_inductive_step(n_int);
            lemma_special_factorial_positive(n_int);
        }
        let result = match prev.checked_mul(fact_result as i8) {
            Some(val) => val,
            None => {
                proof {
                    assert(special_factorial_func(k as int) >= 1);
                    assert(factorial_func(n_int) >= 1);
                    assert(special_factorial_func(n_int) as int >= 1);
                    assert(false);
                }
                panic!("Overflow in special_factorial");
            }
        };
        assert(result as int == special_factorial_func(n_int));
        assert(result > 0);
        result
    }
}
// </vc-code>


}

fn main() {}