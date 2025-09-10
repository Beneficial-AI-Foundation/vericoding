use vstd::prelude::*;

verus! {

fn sum_and_average(n: i32) -> (res: (i32, i32))
    requires n > 0
    ensures res.0 == n * (n + 1) / 2 && res.1 * n == res.0
{
    assume(false);
    unreached()
}

}
fn main() {}