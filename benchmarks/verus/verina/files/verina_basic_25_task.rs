use vstd::prelude::*;

verus! {

fn sum_and_average(n: u32) -> (result: (u32, f64))
    requires n < 100000,
    ensures
        n == 0 ==> result.0 == 0,
        n > 0 ==> result.0 == (n * (n + 1)) / 2,
{
    assume(false);
    unreached();
}

}
fn main() {}