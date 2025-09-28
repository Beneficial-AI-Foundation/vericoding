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
/* helper modified by LLM (iteration 5): fixed proofs by adding proper inductive reasoning and bounds calculations */
proof fn sum_odd_at_even_positions_monotonic(lst: Seq<int>, pos1: int, pos2: int)
    requires
        pos1 <= pos2,
        pos1 >= 0,
        pos2 >= 0,
        pos1 % 2 == 0,
        pos2 % 2 == 0,
    ensures
        sum_odd_at_even_positions(lst, pos1) >= sum_odd_at_even_positions(lst, pos2)
{
    if pos1 >= lst.len() {
        return;
    }
    if pos2 >= lst.len() {
        return;
    }
    if pos1 == pos2 {
        return;
    }
    
    sum_odd_at_even_positions_monotonic(lst, pos1 + 2, pos2);
}

proof fn sum_odd_at_even_positions_bounds(lst: Seq<int>, pos: int)
    requires
        pos >= 0,
        pos % 2 == 0,
        forall|i: int| 0 <= i < lst.len() ==> -128 <= lst[i] <= 127,
    ensures
        -128 * ((lst.len() + 1) / 2) <= sum_odd_at_even_positions(lst, pos) <= 127 * ((lst.len() + 1) / 2)
{
    if pos >= lst.len() {
        return;
    }
    
    sum_odd_at_even_positions_bounds(lst, pos + 2);
    
    if lst[pos] % 2 == 1 {
        assert(-128 <= lst[pos] <= 127);
    }
}

proof fn sum_equivalence(lst: Seq<int>, pos: int, result: i8, i: int)
    requires
        pos == 0,
        i <= lst.len(),
        i % 2 == 0,
        forall|j: int| 0 <= j < lst.len() ==> -128 <= lst[j] <= 127,
        result as int == sum_odd_at_even_positions(lst.subrange(0, i as int), 0),
    ensures
        sum_odd_at_even_positions(lst, i as int) + result as int == sum_odd_at_even_positions(lst, 0)
{
    if i >= lst.len() {
        return;
    }
    
    sum_equivalence(lst, pos, result, i + 2);
}
// </vc-helpers>

// <vc-spec>
fn solution(lst: Vec<i8>) -> (result: i8)
    requires lst@.len() > 0
    ensures result as int == sum_odd_at_even_positions(lst@.map(|i: int, x: i8| x as int), 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed invalid ghost type usage in exec code */
    let mut result: i8 = 0;
    let mut i: usize = 0;
    
    proof {
        let mapped_lst = lst@.map(|idx: int, x: i8| x as int);
    }
    
    while i < lst.len()
        invariant
            i <= lst.len(),
            i % 2 == 0,
            -128 * ((lst@.len() + 1) / 2) <= result as int <= 127 * ((lst@.len() + 1) / 2),
            result as int + sum_odd_at_even_positions(lst@.map(|idx: int, x: i8| x as int), i as int) == sum_odd_at_even_positions(lst@.map(|idx: int, x: i8| x as int), 0),
        decreases lst.len() - i
    {
        if lst[i] % 2 == 1 {
            assert(-128 <= lst[i] as int <= 127);
            assert(-128 <= result as int + lst[i] as int <= 127);
            result = result + lst[i];
        }
        assert(i + 2 <= lst.len() + 1);
        i = i + 2;
    }
    
    result
}
// </vc-code>


}

fn main() {}