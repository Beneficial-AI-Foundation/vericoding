use vstd::prelude::*;

verus! {

#[verifier::memoize]
spec fn spec_fib(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        1
    } else {
        spec_fib((n - 1) as nat) + spec_fib((n - 2) as nat)
    }
}
// pure-end
// pure-end

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// pure-end

// <vc-helpers>
// No updates needed in helpers
// </vc-helpers>

// <vc-spec>
fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
// </vc-spec>
// <vc-code>
fn fib(n: u32) -> (ret: Option<u32>)
    ensures
        inner_expr_fib(n, ret),
{
    fib_rec(n)
}

fn fib_rec(n: u32) -> (ret: Option<u32>)
    decreases n,
    ensures
        inner_expr_fib(n, ret),
{
    if n == 0 {
        Some(0)
    } else if n == 1 {
        Some(1)
    } else {
        if let Some(p1) = fib_rec(n - 1) {
            if let Some(p2) = fib_rec(n - 2) {
                match p1.checked_add(p2) {
                    Some(sum) => Some(sum),
                    None => None,
                }
            } else {
                None
            }
        } else {
            None
        }
    }
}
// </vc-code>

} // verus!
fn main() {}