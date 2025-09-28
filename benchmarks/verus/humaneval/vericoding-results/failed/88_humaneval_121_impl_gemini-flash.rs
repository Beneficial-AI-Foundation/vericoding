// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_odd_at_even_positions(lst: Seq<int>, pos: int) -> int
    decreases if pos < lst.len() { lst.len() - pos } else { 0 }
{
    if pos >= lst.len() {
        0
    } else if lst[pos] % 2 == 1 {
        lst[pos] + sum_odd_at_even_positions(lst, pos + 2)
    } else {
        sum_odd_at_even_positions(lst, pos + 2)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a function for sum of odd elements at even positions up to a given index */

spec fn sum_odd_at_even_positions_upto(lst: Seq<int>, start_pos: int, end_pos: int) -> int
    requires
        0 <= start_pos <= lst.len(),
        0 <= end_pos <= lst.len(),
        start_pos % 2 == 0,
        end_pos % 2 == 0,
        start_pos <= end_pos,
    decreases (end_pos - start_pos) / 2
{
    if start_pos >= end_pos {
        0
    } else if lst[start_pos] % 2 == 1 {
        lst[start_pos] + sum_odd_at_even_positions_upto(lst, start_pos + 2, end_pos)
    } else {
        sum_odd_at_even_positions_upto(lst, start_pos + 2, end_pos)
    }
}
// </vc-helpers>

// <vc-spec>
fn solution(lst: Vec<i8>) -> (result: i8)
    requires lst@.len() > 0
    ensures result as int == sum_odd_at_even_positions(lst@.map(|i: int, x: i8| x as int), 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix for postcondition and invariant not satisfied, as well as arithmetic overflow. */
{
    let mut total: i8 = 0;
    let mut i: usize = 0;

    while i < lst.len()
        invariant
            i % 2 == 0,
            i <= lst.len(),
            total as int == sum_odd_at_even_positions_upto(lst@.map(|_, x| x as int), 0, i as int),
            0 <= total,
            total <= 127,
        decreases (lst.len() - i) as int
    {
        if lst[i] % 2 != 0 {
            total = total + lst[i];
        }

        i = i + 2;
    }
    total
}
// </vc-code>


}

fn main() {}