// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 2 && n % 2 == 0 && n <= 20
}

spec fn factorial(n: int) -> int
    decreases n
{
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}

spec fn expected_result(n: int) -> int {
    if valid_input(n) {
        let half = n / 2;
        let fact_n = factorial(n);
        let fact_half = factorial(half);
        let fact_half_minus_1 = factorial(half - 1);
        let binomial = fact_n / (fact_half * fact_half);
        let arrangements = fact_half_minus_1 * fact_half_minus_1;
        (binomial * arrangements) / 2
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed factorial lemmas and bounds, added proper overflow checks */
proof fn lemma_factorial_positive(n: int)
    requires n >= 0
    ensures factorial(n) > 0
    decreases n
{
    if n <= 1 {
        assert(factorial(0) == 1);
        assert(factorial(1) == 1);
    } else {
        lemma_factorial_positive(n - 1);
        assert(factorial(n - 1) > 0);
        assert(n > 0);
        assert(factorial(n) == n * factorial(n - 1));
    }
}

proof fn lemma_factorial_2() 
    ensures factorial(2) == 2
{
    assert(factorial(2) == 2 * factorial(1));
    assert(factorial(1) == 1);
}

proof fn lemma_factorial_3()
    ensures factorial(3) == 6
{
    assert(factorial(3) == 3 * factorial(2));
    lemma_factorial_2();
}

proof fn lemma_factorial_4()
    ensures factorial(4) == 24
{
    assert(factorial(4) == 4 * factorial(3));
    lemma_factorial_3();
}

proof fn lemma_factorial_5()
    ensures factorial(5) == 120
{
    assert(factorial(5) == 5 * factorial(4));
    lemma_factorial_4();
}

proof fn lemma_factorial_6()
    ensures factorial(6) == 720
{
    assert(factorial(6) == 6 * factorial(5));
    lemma_factorial_5();
}

proof fn lemma_factorial_7()
    ensures factorial(7) == 5040
{
    assert(factorial(7) == 7 * factorial(6));
    lemma_factorial_6();
}

proof fn lemma_factorial_8()
    ensures factorial(8) == 40320
{
    assert(factorial(8) == 8 * factorial(7));
    lemma_factorial_7();
}

proof fn lemma_factorial_9()
    ensures factorial(9) == 362880
{
    assert(factorial(9) == 9 * factorial(8));
    lemma_factorial_8();
}

proof fn lemma_factorial_10()
    ensures factorial(10) == 3628800
{
    assert(factorial(10) == 10 * factorial(9));
    lemma_factorial_9();
}

proof fn lemma_factorial_bounds(n: int)
    requires 0 <= n <= 20
    ensures factorial(n) <= 2432902008176640000
{
    if n <= 0 {
        assert(factorial(0) == 1);
    } else if n <= 1 {
        assert(factorial(1) == 1);
    } else if n <= 2 {
        lemma_factorial_2();
    } else if n <= 3 {
        lemma_factorial_3();
    } else if n <= 4 {
        lemma_factorial_4();
    } else if n <= 5 {
        lemma_factorial_5();
    } else if n <= 6 {
        lemma_factorial_6();
    } else if n <= 7 {
        lemma_factorial_7();
    } else if n <= 8 {
        lemma_factorial_8();
    } else if n <= 9 {
        lemma_factorial_9();
    } else if n <= 10 {
        lemma_factorial_10();
    } else {
        assert(factorial(n) <= 2432902008176640000) by (nonlinear_arith)
            requires 0 <= n <= 20;
    }
}

fn compute_factorial(n: i8) -> (result: i64)
    requires 0 <= n <= 20
    ensures result as int == factorial(n as int)
{
    if n <= 1 {
        return 1;
    }
    let mut result: i64 = 1;
    let mut i: i8 = 2;
    
    while i <= n
        invariant
            2 <= i <= n + 1,
            i <= 21,
            result as int == factorial((i - 1) as int),
            result > 0,
            factorial((i - 1) as int) <= 2432902008176640000,
        decreases (n - i) as int
    {
        proof {
            lemma_factorial_positive((i - 1) as int);
            lemma_factorial_positive(i as int);
            assert(i <= n);
            assert(n <= 20);
            assert(i <= 20);
            lemma_factorial_bounds(i as int);
            assert(factorial(i as int) <= 2432902008176640000);
            assert(result * (i as i64) <= i64::MAX);
        }
        result = result * (i as i64);
        i = (i + 1) as i8;
    }
    result
}

proof fn lemma_result_bound(n: int)
    requires valid_input(n)
    ensures expected_result(n) <= 127
{
    assert(n <= 20);
    if n == 2 {
        assert(factorial(2) == 2);
        assert(factorial(1) == 1);
        assert(factorial(0) == 1);
        assert(expected_result(2) == (2 / (1 * 1) * (1 * 1)) / 2);
        assert(expected_result(2) == 1);
    } else if n == 4 {
        assert(factorial(4) == 24);
        assert(factorial(2) == 2);
        assert(factorial(1) == 1);
        assert(expected_result(4) == (24 / (2 * 2) * (1 * 1)) / 2);
        assert(expected_result(4) == 3);
    } else if n == 6 {
        assert(factorial(6) == 720);
        assert(factorial(3) == 6);
        assert(factorial(2) == 2);
        assert(expected_result(6) == (720 / (6 * 6) * (2 * 2)) / 2);
        assert(expected_result(6) == 10);
    } else if n == 8 {
        assert(factorial(8) == 40320);
        assert(factorial(4) == 24);
        assert(factorial(3) == 6);
        assert(expected_result(8) == (40320 / (24 * 24) * (6 * 6)) / 2);
        assert(expected_result(8) == 35);
    } else if n == 10 {
        assert(factorial(10) == 3628800);
        assert(factorial(5) == 120);
        assert(factorial(4) == 24);
        assert(expected_result(10) == (3628800 / (120 * 120) * (24 * 24)) / 2);
        assert(expected_result(10) == 126);
    } else {
        assert(expected_result(n) <= 127) by (nonlinear_arith)
            requires valid_input(n);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == expected_result(n as int) && result > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed overflow issues with proper intermediate computations */
    let half = (n / 2) as i8;
    
    proof {
        lemma_factorial_positive(n as int);
        lemma_factorial_positive(half as int);
        lemma_factorial_positive((half - 1) as int);
        lemma_factorial_bounds(n as int);
        lemma_factorial_bounds(half as int);
        lemma_factorial_bounds((half - 1) as int);
        
        if n == 2 {
            lemma_factorial_2();
            assert(factorial(1) == 1);
            assert(factorial(0) == 1);
        } else if n == 4 {
            lemma_factorial_4();
            lemma_factorial_2();
            assert(factorial(1) == 1);
        } else if n == 6 {
            lemma_factorial_6();
            lemma_factorial_3();
            lemma_factorial_2();
        } else if n == 8 {
            lemma_factorial_8();
            lemma_factorial_4();
            lemma_factorial_3();
        } else if n == 10 {
            lemma_factorial_10();
            lemma_factorial_5();
            lemma_factorial_4();
        }
    }
    
    let fact_n = compute_factorial(n);
    let fact_half = compute_factorial(half);
    let fact_half_minus_1 = compute_factorial(half - 1);
    
    proof {
        assert(fact_half > 0);
        assert(fact_half_minus_1 > 0);
        lemma_factorial_bounds(half as int);
        lemma_factorial_bounds((half - 1) as int);
        assert(fact_half <= 3628800); // max is factorial(10)
        assert(fact_half_minus_1 <= 362880); // max is factorial(9)
        assert(fact_half * fact_half <= i64::MAX);
        assert(fact_half_minus_1 * fact_half_minus_1 <= i64::MAX);
    }
    
    let denominator = fact_half * fact_half;
    let binomial = fact_n / denominator;
    let arrangements = fact_half_minus_1 * fact_half_minus_1;
    
    proof {
        assert(binomial <= fact_n);
        assert(arrangements <= 362880 * 362880);
        assert(binomial * arrangements <= i64::MAX);
    }
    
    let result = (binomial * arrangements) / 2;
    
    proof {
        assert(fact_n as int == factorial(n as int));
        assert(fact_half as int == factorial(half as int));
        assert(fact_half_minus_1 as int == factorial((half - 1) as int));
        
        let expected = expected_result(n as int);
        assert(expected == (factorial(n as int) / (factorial(half as int) * factorial(half as int)) * 
                           (factorial((half - 1) as int) * factorial((half - 1) as int))) / 2);
        
        assert(binomial as int == factorial(n as int) / (factorial(half as int) * factorial(half as int)));
        assert(arrangements as int == factorial((half - 1) as int) * factorial((half - 1) as int));
        assert(result as int == (binomial * arrangements / 2) as int);
        assert(result as int == expected);
        assert(result > 0);
        lemma_result_bound(n as int);
        assert(result <= 127);
    }
    
    result as i8
}
// </vc-code>


}

fn main() {}