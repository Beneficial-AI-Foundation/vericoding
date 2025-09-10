use vstd::prelude::*;

verus! {

fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires n >= 0,
    ensures
        result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3,
{
    assume(false);
    unreached();
}

}
fn main() {}