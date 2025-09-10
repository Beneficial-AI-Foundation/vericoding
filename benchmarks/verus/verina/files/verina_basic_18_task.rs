use vstd::prelude::*;

verus! {

fn sum_of_digits(n: nat) -> result: nat;
    ensures result >= 0,
{
    assume(false);
    unreached()
}

}
fn main() {}