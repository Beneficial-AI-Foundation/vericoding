// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed index 'i' to int to fix compilation error and for consistency */
spec fn search_from(sub: Seq<int>, main: Seq<int>, i: int) -> (result: bool)
    requires
        sub.len() <= main.len(),
        0 <= i <= main.len() - sub.len() + 1,
    ensures
        result == exists|k: int| i <= k && k <= main.len() - sub.len() && sub =~= main.subrange(k, k + sub.len()),
    decreases (main.len() - sub.len() + 1) - i,
{
    if i > main.len() - sub.len() {
        false
    } else if main.subrange(i, i + sub.len()) =~= sub {
        true
    } else {
        search_from(sub, main, i + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == exists|i: int, j: int| 0 <= i <= main.len() - sub.len() && j == i + sub.len() && sub =~= #[trigger] main.subrange(i, j)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): call to helper now uses an int index, matching the updated helper signature */
    if sub.len() > main.len() {
        false
    } else {
        search_from(sub, main, 0)
    }
}
// </vc-code>

}
fn main() {}