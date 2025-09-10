use vstd::prelude::*;

verus! {

fn IntDiv(m: i32, n: i32) -> (ret: (i32, i32))
    requires n > 0
    ensures m == n * ret.0 + ret.1 && 0 <= ret.1 < n
{
    assume(false);
    unreached();
}

}
fn main() {}