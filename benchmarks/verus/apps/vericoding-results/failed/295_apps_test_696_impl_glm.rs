// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(p: int) -> bool {
    2 <= p < 2000
}

spec fn count_primitive_roots(p: int) -> int
    recommends valid_input(p)
{
    if p == 2 { 
        1 
    } else { 
        /* Count of integers i where 1 <= i < p-1 and 
           for all j where 2 <= j <= i, not ((p-1) % j == 0 && i % j == 0) */
        Set::new(|i: int| 1 <= i < p-1 && (forall|j: int| 2 <= j <= i ==> !((p-1) % j == 0 && #[trigger] (i % j) == 0))).len() as int
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed invariant syntax with comma and closure braces */
spec fn euler_totient(n: nat) -> nat {
    if n == 1 {
        1
    } else {
        Set::new(|i: nat| { 1 <= i <= n && gcd(i, n) == 1 }).len()
    }
}

/* helper modified by LLM (iteration 5): fixed closure braces in invariant (removed inner braces) */
fn totient(n: nat) -> (result: nat)
    requires n >= 1
    ensures result == euler_totient(n)
{
    let mut count = 0;
    let mut i = 1;
    while i <= n
        invariant 1 <= i <= n+1,
        invariant count == Set::new(|j: nat| 1 <= j < i && gcd(j, n)==1).len(),
        decreases n - i
    {
        if gcd(i, n) == 1 {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(p: i8) -> (result: i8)
    requires valid_input(p as int)
    ensures 
        result >= 0 &&
        result as int == count_primitive_roots(p as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed */
    let n = (p as int) - 1;
    let result_nat = totient(n as nat);
    result_nat as i8
}
// </vc-code>


}

fn main() {}