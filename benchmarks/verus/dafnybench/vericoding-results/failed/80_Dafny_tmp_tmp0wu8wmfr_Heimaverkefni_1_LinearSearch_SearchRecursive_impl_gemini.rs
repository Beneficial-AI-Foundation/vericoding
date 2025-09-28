// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn search_recursive(a: Seq<int>, i: usize, j: usize, x: int) -> (result: isize)
    requires 
        i <= j,
        j <= a.len(),
    ensures
        (i <= result && result < j as isize) || result == -1,
        result != -1 ==> a[result as int] == x,
        result != -1 ==> forall|r: int| result < r && r < j as int ==> a[r] != x,
        result == -1 ==> forall|r: int| i as int <= r && r < j as int ==> a[r] != x,
    decreases j - i,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [fixed sequence indexing from [] to @[]] */
    if i >= j {
        -1
    } else if a@[j - 1] == x {
        (j - 1) as isize
    } else {
        search_recursive(a, i, j - 1, x)
    }
}
// </vc-code>

}
fn main() {}