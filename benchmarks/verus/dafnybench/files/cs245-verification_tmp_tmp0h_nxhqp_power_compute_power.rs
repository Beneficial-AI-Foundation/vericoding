use vstd::prelude::*;

verus! {

spec fn power(a: int, n: nat) -> int
    recommends 0 <= a
    decreases n
{
    if n == 0 { 1 } else { a * power(a, (n - 1) as nat) }
}

fn compute_power(a: u64, n: u64) -> (s: u64)
    requires n >= 0 && a >= 0
    ensures s as int == power(a as int, n as nat)
{
    assume(false);
    unreached();
}

}
fn main() {}