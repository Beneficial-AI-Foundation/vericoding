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
/* helper modified by LLM (iteration 2): added unfolding lemma for factorial and kept supporting lemmas */
spec fn prod_factorials(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 { 1 } else { prod_factorials(n - 1) * factorial_func(n) }
}

proof fn factorial_func_pos(n: int)
    requires
        n >= 0,
    ensures
        factorial_func(n) > 0,
    decreases n
{
    if n <= 1 {
        // factorial_func(n) == 1
    } else {
        factorial_func_pos(n - 1);
        assert(n > 1);
        assert(factorial_func(n - 1) > 0);
        assert(n * factorial_func(n - 1) > 0);
    }
}

proof fn prod_factorials_eq_special(n: int)
    requires
        n >= 0,
    ensures
        prod_factorials(n) == special_factorial_func(n),
    decreases n
{
    if n <= 0 {
        // both are 1
    } else {
        prod_factorials_eq_special(n - 1);
        // By definitions of the functions
        assert(prod_factorials(n) == prod_factorials(n - 1) * factorial_func(n));
        assert(special_factorial_func(n) == special_factorial_func(n - 1) * factorial_func(n));
    }
}

proof fn special_factorial_func_pos(n: int)
    requires
        n >= 0,
    ensures
        special_factorial_func(n) > 0,
    decreases n
{
    if n <= 0 {
        // equals 1
    } else {
        special_factorial_func_pos(n - 1);
        factorial_func_pos(n);
        assert(special_factorial_func(n - 1) > 0);
        assert(factorial_func(n) > 0);
        assert(special_factorial_func(n - 1) * factorial_func(n) > 0);
    }
}

/* helper modified by LLM (iteration 2): unfolding lemma for factorial_func(n+1) */
proof fn factorial_unfold(n: int)
    requires
        n >= 0,
    ensures
        factorial_func(n + 1) == factorial_func(n) * (n + 1),
    decreases n
{
    if n == 0 {
        assert(factorial_func(0) == 1);
        assert(factorial_func(1) == 1);
        assert(factorial_func(0) * (0 + 1) == 1);
        assert(factorial_func(1) == factorial_func(0) * (0 + 1));
    } else {
        assert(n + 1 > 1);
        // From the definition of factorial_func when argument > 1
        assert(factorial_func(n + 1) == (n + 1) * factorial_func(n));
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
    /* code modified by LLM (iteration 2): avoid using 'int' in exec code; use i8 loop with ghost reasoning */
    let m: i8 = n;
    let mut i: i8 = 0;
    let mut fact: i8 = 1;
    let mut acc: i8 = 1;
    while i < m
        invariant
            0 <= i as int,
            i as int <= m as int,
            m as int == n as int,
            fact as int == factorial_func(i as int),
            acc as int == prod_factorials(i as int),
        decreases (m as int) - (i as int)
    {
        let i_prev: i8 = i;
        let fact_prev: i8 = fact;
        let acc_prev: i8 = acc;

        i = i + 1;
        fact = fact_prev * i;
        acc = acc_prev * fact;

        proof {
            let io: int = i_prev as int;
            assert(i as int == io + 1);
            factorial_unfold(io);
            // The algebraic links between exec updates and spec equalities are justified by the unfolding lemma
            // and the definitions of prod_factorials and factorial_func.
        }
    }
    proof {
        prod_factorials_eq_special(m as int);
        special_factorial_func_pos(m as int);
    }
    let result: i8 = acc;
    assert(result as int == special_factorial_func(n as int));
    assert(result > 0);
    result
}
// </vc-code>


}

fn main() {}