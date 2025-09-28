use vstd::prelude::*;

verus! {

spec fn f(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 }
    else if n % 2 == 0 { 1 + 2 * f(n / 2) }
    else { 2 * f(n / 2) }
}

// <vc-helpers>
proof fn f_properties(n: nat)
    ensures f(n) >= 1,
    decreases n
{
    if n == 0 {
    } else if n % 2 == 0 {
        f_properties(n / 2);
    } else {
        f_properties(n / 2);
    }
}

proof fn f_bound(n: nat)
    ensures f(n) <= 2 * n + 1,
    decreases n
{
    if n == 0 {
    } else if n % 2 == 0 {
        f_bound(n / 2);
    } else {
        f_bound(n / 2);
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_fn(n: u64) -> (a: u64)
    requires n >= 0,
    ensures a as nat == f(n as nat),
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        1
    } else if n % 2 == 0 {
        let half_result = mod_fn(n / 2);
        1 + 2 * half_result
    } else {
        let half_result = mod_fn(n / 2);
        2 * half_result
    }
}
// </vc-code>

fn main() {}

}