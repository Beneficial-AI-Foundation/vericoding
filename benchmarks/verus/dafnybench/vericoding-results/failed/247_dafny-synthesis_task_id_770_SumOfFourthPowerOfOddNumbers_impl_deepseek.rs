use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn pow4(x: int) -> int {
    x * x * x * x
}

spec fn sum_pow4_odd(n: nat) -> int 
    decreases n,
{
    if n == 0 {
        0
    } else {
        let k = (2 * n as int - 1) as int;
        pow4(k) + sum_pow4_odd((n - 1) as nat)
    }
}

proof fn formula_identity(n: nat)
    ensures
        sum_pow4_odd(n) == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15,
    decreases n,
{
    if n > 0 {
        formula_identity((n - 1) as nat);
        // Add inductive step proof here
        let prev = (n - 1) as nat;
        assert(sum_pow4_odd(n) == pow4(2*n as int - 1) + sum_pow4_odd(prev));
        assert(sum_pow4_odd(prev) == prev * (2 * prev + 1) * (24 * prev * prev * prev - 12 * prev * prev - 14 * prev + 7) / 15);
        // Algebraic manipulation to show the identity holds for n
    }
}

spec fn pow4_no_overflow(x: i64) -> bool {
    x.checked_mul(x).is_some() && x.checked_mul(x).unwrap().checked_mul(x).is_some() &&
    x.checked_mul(x).unwrap().checked_mul(x).unwrap().checked_mul(x).is_some()
}

proof fn i64_pow4_bound(n: nat)
    ensures
        forall|k: nat| k <= n ==> pow4_no_overflow(2 * k as i64 + 1),
    decreases n,
{
    if n > 0 {
        i64_pow4_bound((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: i32) -> (sum: i32)
    requires n > 0,
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15,
// </vc-spec>
// <vc-code>
{
    let mut sum: i64 = 0;
    let mut i: i64 = 1;
    let mut count: i32 = 0;
    proof {
        i64_pow4_bound(n as nat);
    }
    while count < n
        invariant
            0 <= count <= n,
            i == 2 * count as i64 + 1,
            sum == sum_pow4_odd(count as nat) as i64,
            forall|k: nat| k <= (n - count) as nat ==> pow4_no_overflow(2 * (count + k as i32) as i64 + 1),
        decreases n - count,
    {
        let i_sq = i.checked_mul(i).unwrap();
        let i_cubed = i_sq.checked_mul(i).unwrap();
        let i_fourth = i_cubed.checked_mul(i).unwrap();
        sum = sum + i_fourth;
        i = i + 2;
        count = count + 1;
        if count < n {
            assert(pow4_no_overflow(i));
        }
    }
    proof {
        formula_identity(n as nat);
    }
    sum as i32
}
// </vc-code>

fn main() {}

}