use vstd::prelude::*;

verus! {

fn e() -> (result: f64)
{
    assume(false);
    unreached()
}

}
fn main() {}