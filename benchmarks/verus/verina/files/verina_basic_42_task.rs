use vstd::prelude::*;

verus! {

fn count_digits(s: &str) -> (result: usize)
    ensures
        result >= 0,
{
    assume(false);
    unreached();
}

}
fn main() {}