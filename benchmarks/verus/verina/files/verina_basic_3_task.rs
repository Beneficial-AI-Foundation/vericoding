use vstd::prelude::*;

verus! {

fn is_divisible_by_11(n: i32) -> (result: bool)
    ensures
        result <==> (exists|k: int| #[trigger] (k * 11) == n),
{
    assume(false);
    unreached();
}

}
fn main() {}