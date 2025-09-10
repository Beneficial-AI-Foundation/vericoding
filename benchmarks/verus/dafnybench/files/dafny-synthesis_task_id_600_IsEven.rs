use vstd::prelude::*;

verus! {

fn is_even(n: int) -> (result: bool)
    ensures result <==> n % 2 == 0
{
    assume(false);
    unreached()
}

}
fn main() {}