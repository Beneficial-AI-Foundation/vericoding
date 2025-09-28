// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n && forall|i: int| 0 <= i < n ==> a[i] >= 0
}

spec fn count_survivors(n: int, a: Seq<int>) -> int {
    count_survivors_from(n, a, 0, n)
}

spec fn count_survivors_from(n: int, a: Seq<int>, start: int, left: int) -> int
    decreases n - start
{
    if start >= n {
        0
    } else {
        let i = n - 1 - start;
        let survives: int = if i < left { 1 } else { 0 };
        let new_left: int = if i - a[i] < left { i - a[i] } else { left };
        survives + count_survivors_from(n, a, start + 1, new_left)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed ensures block formatting */
fn recursive_count_survivors_from(n: int, a: Seq<int>, start: int, left: int) -> (count: int)
    requires
        0 <= start <= n,
        left <= n,
        forall|i: int| 0 <= i < n ==> a[i] >= 0,
    decreases n - start,
    ensures
        count == count_survivors_from(n, a, start, left),
{
    if start >= n {
        0
    } else {
        let i = n - 1 - start;
        let survives = if i < left { 1 } else { 0 };
        let new_left = if i - a[i] < left { i - a[i] } else { left };
        survives + recursive_count_survivors_from(n, a, start+1, new_left)
    }
}

/* helper modified by LLM (iteration 5): fixed ensures block formatting */
fn recursive_count_survivors(n: int, a: Seq<int>) -> (count: int)
    requires valid_input(n, a),
    ensures
        count == count_survivors(n, a),
{
    recursive_count_survivors_from(n, a, 0, n)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures result >= 0 && result <= n && result as int == count_survivors(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed */
    let n_int = n as int;
    let a_seq = a@.map_values(|x: i8| x as int);
    let count = recursive_count_survivors(n_int, a_seq);
    count as i8
}
// </vc-code>


}

fn main() {}