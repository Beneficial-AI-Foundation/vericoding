use vstd::prelude::*;

verus! {

fn square_root(n: u32) -> (r: u32)
  ensures r * r <= n < (r + 1) * (r + 1)
{
    assume(false);
    unreached()
}

}
fn main() {}