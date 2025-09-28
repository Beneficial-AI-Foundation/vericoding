// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn calculate_deposit(initial: int, years: int) -> int
    decreases years
{
    if years <= 0 { 
        initial 
    } else { 
        let prev_deposit = calculate_deposit(initial, years - 1);
        prev_deposit + prev_deposit / 100
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemma for lower bound of deposit */
proof fn lemma_deposit_lower_bound(years: nat)
    ensures
        calculate_deposit(100, years as int) >= 100 + years as int,
    decreases years
{
    if years > 0 {
        lemma_deposit_lower_bound((years - 1) as nat);
        let prev_deposit = calculate_deposit(100, (years - 1) as int);
        
        deposit_ge_initial(100, (years - 1) as nat);
        assert(prev_deposit >= 100);

        let current_deposit = calculate_deposit(100, years as int);
        assert(current_deposit == prev_deposit + prev_deposit / 100);
        assert(prev_deposit / 100 >= 1);
        assert(current_deposit >= prev_deposit + 1);
        assert(current_deposit >= (100 + (years - 1) as int) + 1);
    }
}

proof fn deposit_ge_initial(initial: int, years: nat)
    requires
        initial >= 0,
    ensures
        calculate_deposit(initial, years as int) >= initial,
    decreases years
{
    if years > 0 {
        deposit_ge_initial(initial, (years - 1) as nat);
        let prev = calculate_deposit(initial, (years - 1) as int);
        assert(prev >= initial);
        
        let next = calculate_deposit(initial, years as int);
        assert(prev >= 0);
        assert(next == prev + prev / 100);
        assert(next >= prev);
        assert(next >= initial);
    }
}

proof fn deposit_is_strictly_monotonic_100(years: nat)
    ensures
        calculate_deposit(100, (years + 1) as int) > calculate_deposit(100, years as int),
    decreases years
{
    if years > 0 {
        deposit_is_strictly_monotonic_100((years - 1) as nat);
    }
    let current = calculate_deposit(100, years as int);
    deposit_ge_initial(100, years);
    assert(current >= 100);
    
    let next = calculate_deposit(100, (years + 1) as int);
    assert(next == current + current / 100);
    assert(current / 100 >= 1);
    assert(next > current);
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (years: i8)
    requires x >= 101
    ensures 
        years >= 0 &&
        calculate_deposit(100, years as int) >= x as int &&
        (years == 0 || calculate_deposit(100, (years - 1) as int) < x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added invariant and proof for loop termination and postcondition */
    let mut years: i8 = 0;
    let mut deposit: i64 = 100;
    while deposit < x as i64
        invariant
            x >= 101,
            years >= 0,
            years < 127,
            deposit >= 100,
            deposit == calculate_deposit(100, years as int),
            (years > 0 ==> calculate_deposit(100, (years - 1) as int) < x as int),
        decreases (x as i64) - deposit
    {
        proof {
            deposit_is_strictly_monotonic_100(years as nat);
            lemma_deposit_lower_bound(years as nat);
        }
        deposit = deposit + deposit / 100;
        years = years + 1;
    }
    (years)
}
// </vc-code>


}

fn main() {}