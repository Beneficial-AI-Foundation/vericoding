// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] > 0
}

spec fn count_factors_of_two(n: int) -> int
    decreases n when n > 0
{
    if n > 0 && n % 2 == 0 { 1 + count_factors_of_two(n / 2) }
    else { 0 }
}

spec fn sum_factors(a: Seq<int>, i: int) -> int
    decreases a.len() - i when 0 <= i <= a.len()
{
    if 0 <= i < a.len() && (forall|j: int| 0 <= j < a.len() ==> a[j] > 0) {
        count_factors_of_two(a[i]) + sum_factors(a, i + 1)
    } else if i == a.len() {
        0
    } else {
        0
    }
}

spec fn max_operations(a: Seq<int>) -> int {
    if valid_input(a) { sum_factors(a, 0) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>


proof fn lemma_sum_factors_nonnegative(a: Seq<int>, i: int)
    requires
        0 <= i <= a.len(),
        valid_input(a),
    ensures
        sum_factors(a, i) >= 0,
    decreases a.len() - i
{
    if i < a.len() {
        lemma_sum_factors_nonnegative(a, i + 1);
    }
}

proof fn lemma_count_factors_nonnegative(n: int)
    requires
        n >= 0,
    ensures
        count_factors_of_two(n) >= 0,
    decreases n
{
    if n > 0 && n % 2 == 0 {
        lemma_count_factors_nonnegative(n / 2);
    }
}

fn count_factors_of_two_impl(n: i8) -> (result: i8)
    requires
        n >= 0i8,
    ensures
        result >= 0,
        result as int == count_factors_of_two(n as int),
    decreases n as int
{
    if n == 0 {
        0
    } else if n % 2 == 0 {
        let sub_result = count_factors_of_two_impl(n / 2);
        assert(1 + sub_result >= 0) by {
            lemma_count_factors_nonnegative(n as int);
        }
        (1 + sub_result)
    } else {
        0
    }
}


// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(a@.map(|i, x| x as int)),
    ensures 
        result >= 0,
        result as int == max_operations(a@.map(|i, x| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type safety and arithmetic overflow */
    let mut i: usize = 0;
    let mut total: i8 = 0;
    
    proof {
        lemma_sum_factors_nonnegative(a@.map(|idx, x| x as int), 0);
    }
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            total >= 0,
            total as int == sum_factors(a@.map(|idx, x| x as int), i as int),
        decreases a.len() - i
    {
        let current = a[i];
        proof {
            lemma_count_factors_nonnegative(current as int);
        }
        let factors = count_factors_of_two_impl(current);
        assert(total + factors >= 0) by {
            assert(total >= 0);
            assert(factors >= 0);
        };
        total = total + factors;
        i = i + 1;
    }
    
    total
}
// </vc-code>


}

fn main() {}