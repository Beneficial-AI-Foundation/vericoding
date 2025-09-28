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
proof fn lemma_sum_odd_at_even_positions_nonnegative(lst: Seq<int>, pos: int)
    requires 
        pos >= 0,
    ensures 
        sum_odd_at_even_positions(lst, pos) >= 0,
    decreases if pos < lst.len() { lst.len() - pos } else { 0 }
{
    if pos < lst.len() {
        lemma_sum_odd_at_even_positions_nonnegative(lst, pos + 2);
    }
}
// </vc-helpers>

// <vc-spec>
fn solution(lst: Vec<i8>) -> (result: i8)
    requires lst@.len() > 0
    ensures result as int == sum_odd_at_even_positions(lst@.map(|i: int, x: i8| x as int), 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix compilation error by using i8 arithmetic without int conversion */
    let mut result: i8 = 0;
    let mut i: usize = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            result as int == sum_odd_at_even_positions(lst@.map(|j: int, x: i8| x as int), 0) - sum_odd_at_even_positions(lst@.map(|j: int, x: i8| x as int), i as int),
        decreases lst.len() - i
    {
        if i % 2 == 0 && lst[i] % 2 == 1 {
            proof { lemma_sum_odd_at_even_positions_nonnegative(lst@.map(|j: int, x: i8| x as int), (i + 1) as int); }
            result = result + lst[i];
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}