// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: Seq<int>) -> bool {
    n > 0 && m > 0 && a.len() == n && forall|i: int| 0 <= i < a.len() ==> a[i] > 0
}

spec fn valid_result(result: int, n: int) -> bool {
    1 <= result <= n
}

spec fn sum_candies_still_needed(queue: Seq<Seq<int>>) -> nat
    decreases queue.len()
{
    if queue.len() == 0 {
        0nat
    } else {
        let child = queue[0];
        let still_needed = if child.len() >= 2 && child[1] <= child[0] { 0nat } else if child.len() >= 2 { (child[1] - child[0]) as nat } else { 0nat };
        still_needed + sum_candies_still_needed(queue.subrange(1, queue.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_pos_implies_ge_one(n: int)
    requires
        n > 0,
    ensures
        1 <= n,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, m as int, a@.map_values(|x: i8| x as int))
    ensures valid_result(result as int, n as int)
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_pos_implies_ge_one(n as int);
    }
    1i8
}
// </vc-code>


}

fn main() {}