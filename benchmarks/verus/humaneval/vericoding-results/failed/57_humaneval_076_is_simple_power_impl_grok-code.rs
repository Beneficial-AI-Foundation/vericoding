// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * power(x, (y - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_simple_power(x: u8, n: i8) -> (ans: bool)
    requires x > 0
    ensures ans <==> exists|y: nat| n as int == power(x as nat, y) as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop logic to properly check if n is a perfect power of x with overflow check */
    if x == 1u8 {
        return n as int == 1;
    }
    if n <= 0 {
        return false;
    }
    let mut curr: i64 = 1;
    while curr < n as i64 {
        let mut next: i64 = curr;
        next *= x as i64;
        if next <= curr {
            return false;
        }
        curr = next;
        if curr == n as i64 {
            return true;
        }
    }
    if curr == n as i64 {
        return true;
    }
    false
}
// </vc-code>


}

fn main() {}