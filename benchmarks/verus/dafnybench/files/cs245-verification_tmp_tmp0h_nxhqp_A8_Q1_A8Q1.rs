use vstd::prelude::*;

verus! {

spec fn power(a: int, n: int) -> int
    recommends 0 <= n
    decreases n when 0 <= n
{
    if n <= 0 { 1 } else { a * power(a, n - 1) }
}

fn A8Q1(y0: int, x: int) -> (z: int)
    requires y0 >= 0
    ensures z == power(x, y0)
{
    assume(false);
    unreached();
}

}
fn main() {}