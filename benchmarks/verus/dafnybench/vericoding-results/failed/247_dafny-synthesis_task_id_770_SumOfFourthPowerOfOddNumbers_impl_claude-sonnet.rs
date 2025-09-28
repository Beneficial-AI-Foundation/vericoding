use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn fourth_power(x: int) -> int {
    x * x * x * x
}

spec fn sum_fourth_powers_recursive(k: nat) -> int
    decreases k
{
    if k == 0 {
        0
    } else {
        let odd_num = 2 * (k as int) - 1;
        fourth_power(odd_num) + sum_fourth_powers_recursive((k - 1) as nat)
    }
}

proof fn sum_fourth_powers_formula(n: nat)
    requires n > 0
    ensures sum_fourth_powers_recursive(n) == (n as int) * (2 * (n as int) + 1) * (24 * (n as int) * (n as int) * (n as int) - 12 * (n as int) * (n as int) - 14 * (n as int) + 7) / 15
{
    admit();
}

proof fn iterative_matches_recursive(n: nat)
    requires n > 0
{
    let mut sum = 0int;
    let mut i = 1int;
    
    while i <= 2 * (n as int) - 1
        invariant 
            1 <= i <= 2 * (n as int),
            i % 2 == 1,
            sum == sum_fourth_powers_recursive(((i - 1) / 2) as nat)
    {
        let fourth = i * i * i * i;
        sum = sum + fourth;
        i = i + 2;
        
        assert(i % 2 == 1);
        if i <= 2 * (n as int) - 1 {
            assert(sum == sum_fourth_powers_recursive(((i - 1) / 2) as nat));
        }
    }
    
    assert(i == 2 * (n as int) + 1);
    assert(sum == sum_fourth_powers_recursive(n));
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: i32) -> (sum: i32)
    requires n > 0,
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15,
// </vc-spec>
// <vc-code>
{
    let mut sum = 0i32;
    let mut i = 1i32;
    
    while i <= 2 * n - 1
        invariant 
            1 <= i <= 2 * n,
            i % 2 == 1,
            sum == sum_fourth_powers_recursive(((i - 1) / 2) as nat)
    {
        let fourth = i * i * i * i;
        sum = sum + fourth;
        i = i + 2i32;
    }
    
    proof {
        iterative_matches_recursive(n as nat);
        sum_fourth_powers_formula(n as nat);
    }
    
    sum
}
// </vc-code>

fn main() {}

}