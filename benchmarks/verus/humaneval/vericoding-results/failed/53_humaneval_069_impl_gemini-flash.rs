// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

spec fn count(s: Seq<int>, x: int) -> int {
    s.filter(|i: int| i == x).len() as int
}

spec fn max_seq(s: Seq<int>) -> int
    recommends s.len() > 0
{
    if s.len() == 1 { s[0] } else { choose|x: int| s.contains(x) }
}

spec fn valid_input(lst: Seq<int>) -> bool {
    lst.len() > 0 && forall|i: int| 0 <= i < lst.len() ==> lst[i] > 0
}

spec fn valid_result(lst: Seq<int>, result: int) -> bool
    recommends valid_input(lst)
{
    if result == -1 {
        forall|x: int| #![auto] lst.contains(x) ==> count(lst, x) < x
    } else {
        result > 0 &&
        lst.contains(result) && 
        count(lst, result) >= result &&
        forall|y: int| #![auto] lst.contains(y) && count(lst, y) >= y ==> y <= result
    }
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helper fixes needed. */
proof fn lemma_max_is_in_seq(s: Seq<int>)
    requires s.len() > 0
    ensures s.contains(max_seq(s))
{
    // The choose expression in max_seq implicitly guarantees s.contains(max_seq(s))
}
// </vc-helpers>

// <vc-spec>
fn search(lst: Vec<i8>) -> (result: i8)
    requires valid_input(lst@.map(|_index: int, x: i8| x as int))
    ensures valid_result(lst@.map(|_index: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The type conversion `x as int` must happen in ghost code only. Corrected the map function to use `_index: nat` while `x` is `i8`. */
{
    let s_ghost = lst@.map(|_index: nat, x: i8| x as int);

    let mut max_val: int = -1;

    let mut i: nat = 0;
    while i < s_ghost.len()
        invariant 
            0 <= i <= s_ghost.len(),
            max_val == -1 || 
            (
                max_val > 0 && 
                s_ghost.contains(max_val) &&
                count(s_ghost, max_val) >= max_val && 
                forall |y: int| #![auto] (s_ghost.contains(y) && count(s_ghost, y) >= y) ==> y <= max_val
            )
        decreases s_ghost.len() - i
    {
        let current_val = s_ghost[i];
        if current_val > 0 && count(s_ghost, current_val) >= current_val {
            if max_val == -1 || current_val > max_val {
                max_val = current_val;
            }
        }
        i = i + 1;
    }

    let result_i8 = max_val as i8;
    result_i8
}
// </vc-code>


}

fn main() {}