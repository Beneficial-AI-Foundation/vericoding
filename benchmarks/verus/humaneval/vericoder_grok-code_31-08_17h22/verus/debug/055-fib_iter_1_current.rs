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
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    fib_rec(n)
}

fn fib_rec(n: u32) -> (ret: Option<u32>)
    decreases n,
{
    if n == 0 {
        Some(0)
    } else if n == 1 {
        Some(1)
    } else {
        let prev1 = match fib_rec(n - 1) {
            None => None,
            Some(p1) => {
                match fib_rec(n - 2) {
                    None => None,
                    Some(p2) => {
                        match p1.checked_add(p2) {
                            None => None,
                            Some(sum) => Some(sum),
                        }
                    }
                }
            }
        };
        prev1
    }
}
// impl-end
// </vc-code>

} // verus!
fn main() {}