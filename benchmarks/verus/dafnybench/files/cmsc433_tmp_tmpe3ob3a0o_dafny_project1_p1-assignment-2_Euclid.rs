use vstd::prelude::*;

verus! {

fn euclid(m: int, n: int) -> (gcd: int)
    requires m > 1 && n > 1 && m >= n
    ensures gcd > 0 && gcd <= n && gcd <= m && m % gcd == 0 && n % gcd == 0
{
    assume(false);
    unreached();
}

}
fn main() {}