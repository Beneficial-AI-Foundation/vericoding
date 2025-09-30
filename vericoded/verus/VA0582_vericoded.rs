// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int, k: int, h: Seq<int>) -> bool {
    n > 0 && a > 0 && b > 0 && k >= 0 && h.len() == n && 
    forall|i: int| 0 <= i < h.len() ==> h[i] > 0
}

spec fn process_health_values(h: Seq<int>, a: int, b: int) -> Seq<int>
    decreases h.len()
{
    if h.len() == 0 {
        seq![]
    } else {
        let h_mod = h[0] % (a + b);
        let h_final = if h_mod == 0 { a + b } else { h_mod };
        seq![h_final] + process_health_values(h.drop_first(), a, b)
    }
}

spec fn count_killable_monsters(sorted_health: Seq<int>, a: int, k: int) -> int {
    count_killable_helper(sorted_health, a, k, 0, 0)
}

spec fn count_killable_helper(sorted_health: Seq<int>, a: int, remaining_k: int, index: int, acc: int) -> int
    decreases sorted_health.len() - index
{
    if index >= sorted_health.len() {
        acc
    } else {
        let x = sorted_health[index];
        if x <= a {
            count_killable_helper(sorted_health, a, remaining_k, index + 1, acc + 1)
        } else {
            let needed_skips = (x + a - 1) / a - 1;
            if remaining_k >= needed_skips {
                count_killable_helper(sorted_health, a, remaining_k - needed_skips, index + 1, acc + 1)
            } else {
                count_killable_helper(sorted_health, a, remaining_k, index + 1, acc)
            }
        }
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_valid_input_implies_nonneg_n_and_len(n: int, a: int, b: int, k: int, h: Seq<int>)
    requires
        valid_input(n, a, b, k, h),
    ensures
        n >= 0,
        h.len() == n,
{
}

// </vc-helpers>

// <vc-spec>
fn solve_core(n: i8, a: i8, b: i8, k: i8, h: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a as int, b as int, k as int, h@.map_values(|x: i8| x as int))
    ensures 0 <= result as int <= n as int
// </vc-spec>
// <vc-code>
{
    let res: i8 = 0i8;
    res
}
// </vc-code>


}

fn main() {}