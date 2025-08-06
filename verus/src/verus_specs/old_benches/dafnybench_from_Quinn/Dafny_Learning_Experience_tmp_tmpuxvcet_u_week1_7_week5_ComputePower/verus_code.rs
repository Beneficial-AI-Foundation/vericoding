use vstd::prelude::*;

verus! {
    spec fn power(n: nat) -> nat
        decreases n
    {
        if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
    }

    fn calc_power(n: u32) -> (p: u32)
        ensures p as nat == 2 * n
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    fn compute_power(n: u32) -> (p: u32)
        ensures p as nat == power(n as nat)
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}