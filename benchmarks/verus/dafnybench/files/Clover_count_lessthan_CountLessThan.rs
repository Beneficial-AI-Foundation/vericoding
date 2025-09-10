use vstd::prelude::*;

verus! {

fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
{
    assume(false);
    unreached();
}

}
fn main() {}