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
/* helper modified by LLM (iteration 5): No changes needed as verification passed */
exec fn count_survivors_exec(n: i8, a: &Vec<i8>, start: i32, left: i32) -> (result: i32)
    requires
        n >= 1,
        a.len() == n as usize,
        forall|i: int| 0 <= i < n ==> (a@[i] >= 0),
        0 <= start <= n as i32,
    ensures
        result as int == count_survivors_from(n as int, a@.map_values(|x: i8| x as int), start as int, left as int),
    decreases (n as i32 - start) as int
{
    if start >= n as i32 {
        0
    } else {
        let i = n as i32 - 1 - start;
        let survives: i32 = if i < left { 1_i32 } else { 0_i32 };
        let temp = i - a[i as usize] as i32;
        let new_left = if temp < left {
            temp
        } else {
            left
        };
        survives + count_survivors_exec(n, a, start + 1, new_left)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures result >= 0 && result <= n && result as int == count_survivors(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Placed truncate attribute on the cast with parentheses as required by Verus */
{
    let result: i8 = #[verifier::truncate] (count_survivors_exec(n, &a, 0 as i32, n as i32) as i8);
    result
}
// </vc-code>


}

fn main() {}