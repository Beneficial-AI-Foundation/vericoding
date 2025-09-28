// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn num_digits(n: int) -> int
  recommends n >= 1
  decreases n
{
  if n < 10 { 1 } else { 1 + num_digits(n / 10) }
}

spec fn valid_input(n: int) -> bool {
  n >= 1
}

spec fn f(a: int, b: int) -> int
  recommends a >= 1 && b >= 1
{
  let digits_a = num_digits(a);
  let digits_b = num_digits(b);
  if digits_a > digits_b { digits_a } else { digits_b }
}

spec fn is_factor_pair(a: int, b: int, n: int) -> bool {
  a >= 1 && b >= 1 && a * b == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Complete ghost function implementations with proper syntax */
proof fn lemma_num_digits_positive(n: int)
    requires
        n >= 1,
    ensures
        num_digits(n) >= 1,
    decreases n
{
    if n >= 10 {
        lemma_num_digits_positive(n / 10);
    }
}

proof fn lemma_factor_pairs_exist(n: int)
    requires
        n >= 1,
    ensures
        exists|a: int, b: int| is_factor_pair(a, b, n),
{
    assert(is_factor_pair(1, n, n));
}

proof fn lemma_f_monotonic(a1: int, b1: int, a2: int, b2: int)
    requires
        a1 >= 1, b1 >= 1, a2 >= 1, b2 >= 1,
        a1 <= a2, b1 <= b2,
    ensures
        f(a1, b1) <= f(a2, b2),
{
    lemma_num_digits_positive(a1);
    lemma_num_digits_positive(a2);
    lemma_num_digits_positive(b1);
    lemma_num_digits_positive(b2);
}

spec fn candidate_solution(n: int) -> int
    recommends n >= 1
{
    let mut min_f = num_digits(n);
    let mut a = 1;
    while a * a <= n
        invariant
            a >= 1,
            exists|a_val: int, b_val: int| a_val >= a && is_factor_pair(a_val, b_val, n) && f(a_val, b_val) <= min_f,
            forall|a_val: int, b_val: int| a_val < a && is_factor_pair(a_val, b_val, n) ==> f(a_val, b_val) >= min_f,
        decreases n - a
    {
        if n % a == 0 {
            let b = n / a;
            let current_f = f(a, b);
            if current_f < min_f {
                min_f = current_f;
            }
        }
        a = a + 1;
    }
    min_f
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
  requires 
    valid_input(n as int)
  ensures 
    result >= 1,
    exists|a: int, b: int| is_factor_pair(a, b, n as int) && result as int == f(a, b),
    forall|a: int, b: int| is_factor_pair(a, b, n as int) ==> result as int <= f(a, b),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Move variable declarations out of ghost block */
    let n_int = n as int;
    proof {
        let mut result_val = num_digits(n_int);
        let mut a: int = 1;
        
        while a * a <= n_int
            invariant
                a >= 1,
                exists|a_val: int, b_val: int| a_val >= a && is_factor_pair(a_val, b_val, n_int) && f(a_val, b_val) <= result_val,
                forall|a_val: int, b_val: int| a_val < a && is_factor_pair(a_val, b_val, n_int) ==> f(a_val, b_val) >= result_val,
            decreases n_int - a
        {
            if n_int % a == 0 {
                let b = n_int / a;
                let current_f = f(a, b);
                if current_f < result_val {
                    result_val = current_f;
                }
            }
            a = a + 1;
        }
        
        lemma_factor_pairs_exist(n_int);
        lemma_num_digits_positive(n_int);
        assert(result_val >= 1);
        assert(forall|a_val: int, b_val: int| is_factor_pair(a_val, b_val, n_int) ==> result_val <= f(a_val, b_val));
        
        result_val as i8
    }
}
// </vc-code>


}

fn main() {}