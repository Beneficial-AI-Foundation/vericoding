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
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
spec fn vec_to_seq(a: Vec<i8>) -> Seq<int> {
    a@.map_values(|x: i8| x as int)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures result >= 0 && result <= n && result as int == count_survivors(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): maintain invariant relating accumulated result to remaining recursive count */
    let n_i32: i32 = n as i32;
    let mut start: i32 = 0;
    let mut left: i32 = n_i32;
    let mut res: i32 = 0;

    while start < n_i32
        invariant
            0 <= start && start <= n_i32,
            0 <= left && left <= n_i32,
            0 <= res && res <= n_i32,
            res as int + count_survivors_from(n as int, vec_to_seq(a), start as int, left as int) == count_survivors(n as int, vec_to_seq(a)),
        decreases n as int - start as int
    {
        let i: i32 = n_i32 - 1 - start;
        let ai: i32 = a[i as usize] as i32;
        let survives: i32 = if i < left { 1 } else { 0 };
        let new_left: i32 = if i - ai < left { i - ai } else { left };

        res = res + survives;
        left = new_left;
        start = start + 1;
    }

    let result: i8 = res as i8;
    result
}
// </vc-code>


}

fn main() {}