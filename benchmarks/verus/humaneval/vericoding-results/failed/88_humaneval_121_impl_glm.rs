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

// </vc-helpers>

// <vc-spec>
fn solution(lst: Vec<i8>) -> (result: i8)
    requires lst@.len() > 0
    ensures result as int == sum_odd_at_even_positions(lst@.map(|i: int, x: i8| x as int), 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type mismatch in invariant by casting index to int */
    let mut sum = 0i8;
    let mut index = 0;
    while index < lst.len()
        invariant
            0 <= index <= lst.len(),
            sum as int == sum_odd_at_even_positions(lst@.map(|i: int, x: i8| x as int).subrange(0, index as int), 0),
        decreases lst.len() - index
    {
        if index % 2 == 0 && lst[index] % 2 != 0 {
            sum += lst[index];
        }
        index += 1;
    }
    sum
}
// </vc-code>


}

fn main() {}