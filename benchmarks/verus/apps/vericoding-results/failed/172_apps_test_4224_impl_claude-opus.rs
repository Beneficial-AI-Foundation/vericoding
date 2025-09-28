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
proof fn sum_factors_base(a: Seq<int>)
    requires
        valid_input(a),
    ensures
        sum_factors(a, a.len() as int) == 0,
{
    reveal(sum_factors);
}

proof fn sum_factors_step(a: Seq<int>, i: int)
    requires
        valid_input(a),
        0 <= i < a.len(),
    ensures
        sum_factors(a, i) == count_factors_of_two(a[i]) + sum_factors(a, i + 1),
{
    reveal(sum_factors);
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] > 0);
}

/* helper modified by LLM (iteration 5): removed overflow checks to maintain invariant */
fn count_factors_exec(n: i8) -> (result: i8)
    requires
        n > 0,
    ensures
        result >= 0,
        result as int == count_factors_of_two(n as int),
{
    let mut count: i8 = 0;
    let mut m = n;
    
    while m % 2 == 0
        invariant
            m > 0,
            count >= 0,
            count as int + count_factors_of_two(m as int) == count_factors_of_two(n as int),
        decreases m,
    {
        count = count + 1;
        m = m / 2;
    }
    
    count
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
    /* code modified by LLM (iteration 5): removed overflow checks to maintain invariant */
    let mut total: i8 = 0;
    let mut i: usize = 0;
    let ghost a_spec = a@.map(|idx: int, x: i8| x as int);
    
    while i < a.len()
        invariant
            i <= a.len(),
            total >= 0,
            valid_input(a_spec),
            total as int == sum_factors(a_spec, 0) - sum_factors(a_spec, i as int),
            a@ == a@,
            a_spec == a@.map(|idx: int, x: i8| x as int),
        decreases a.len() - i,
    {
        proof {
            sum_factors_step(a_spec, i as int);
        }
        
        let factors = count_factors_exec(a[i]);
        total = total + factors;
        i = i + 1;
    }
    
    proof {
        sum_factors_base(a_spec);
        assert(sum_factors(a_spec, a.len() as int) == 0);
        assert(total as int == sum_factors(a_spec, 0));
        assert(max_operations(a_spec) == sum_factors(a_spec, 0));
    }
    
    total
}
// </vc-code>


}

fn main() {}