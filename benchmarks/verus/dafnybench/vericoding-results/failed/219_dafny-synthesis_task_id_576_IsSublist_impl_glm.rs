use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == exists|i: int, j: int| 0 <= i <= main.len() - sub.len() && j == i + sub.len() && sub =~= #[trigger] main.subrange(i, j)
// </vc-spec>
// <vc-code>
{
    if sub.len() == 0 {
        true
    } else if main.len() < sub.len() {
        false
    } else {
        proof {
            exists|i: int|
                0 <= i &&
                i <= (main.len() as int) - (sub.len() as int) &&
                sub =~= main.subrange(i, i + (sub.len() as int))
        }
    }
}
// </vc-code>

fn main() {
}

}