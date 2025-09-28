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

/* helper modified by LLM (iteration 4): no changes needed, section empty */
// </vc-helpers>

// <vc-spec>
fn solution(lst: Vec<i8>) -> (result: i8)
    requires lst@.len() > 0
    ensures result as int == sum_odd_at_even_positions(lst@.map(|i: int, x: i8| x as int), 0)
// </vc-spec>
// <vc-code>

/* code modified by LLM (iteration 4): fixed compilation by declaring v_int as ghost */
{
    let v = lst@;
    let ghost v_int = v.map(|i: int, x: i8| x as int);
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum as int == sum_odd_at_even_positions(v_int, 0) - sum_odd_at_even_positions(v_int, i as int),
        decreases v.len() - i
    {
        if (v@[i] as i32) % 2 == 1 {
            sum = sum + (v@[i] as i32);
        }
        i = i + 2;
    }
    sum as i8
}
// </vc-code>


}

fn main() {}