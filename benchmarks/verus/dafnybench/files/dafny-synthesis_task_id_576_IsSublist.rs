use vstd::prelude::*;

verus! {

fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == exists|i: int, j: int| 0 <= i <= main.len() - sub.len() && j == i + sub.len() && sub =~= #[trigger] main.subrange(i, j)
{
    assume(false);
    unreached()
}

}
fn main() {}