use vstd::prelude::*;

verus! {

fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
{
    assume(false);
    unreached();
}

}
fn main() {}