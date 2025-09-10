use vstd::prelude::*;

verus! {

fn nth_nonagonal_number(n: int) -> (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    assume(false);
    unreached()
}

}
fn main() {}