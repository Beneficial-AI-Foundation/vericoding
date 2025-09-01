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

// <vc-spec>
fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return Some(0);
    }
    if n == 1 {
        return Some(1);
    }
    let mut i: u32 = 2;
    let mut a: u32 = 0;
    let mut b: u32 = 1;
    #[verifier::proof]
    while i <= n
        invariant
            2u32 <= i <= n + 1u32,
            a as nat == spec_fib((i - 2) as nat),
            b as nat == spec_fib((i - 1) as nat),
        decreases ((n - i) as int)
    {
        match a.checked_add(b) {
            Some(c) => {
                a = b;
                b = c;
            }
            None => {
                return None;
            }
        }
        i = i + 1;
    }
    Some(b)
}
// </vc-code>

} // verus!
fn main() {}