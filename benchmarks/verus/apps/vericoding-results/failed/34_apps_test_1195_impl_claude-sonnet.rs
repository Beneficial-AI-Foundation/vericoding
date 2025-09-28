// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(lst: Seq<int>) -> bool {
    5 <= lst.len() <= 10 &&
    forall|i: int| 0 <= i < lst.len() ==> #[trigger] lst[i] >= 1 && #[trigger] lst[i] <= 32
}

spec fn int_xor(a: int, b: int) -> int {
    let a_bv = a as u32;
    let b_bv = b as u32;
    (a_bv ^ b_bv) as int
}

spec fn min_of_sequence(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        s[0]
    } else {
        let tail_min = min_of_sequence(s.skip(1));
        if s[0] <= tail_min {
            s[0]
        } else {
            tail_min
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to recursive proof functions */
proof fn lemma_min_of_sequence_properties(s: Seq<int>)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> min_of_sequence(s) <= s[i]
    decreases s.len()
{
    if s.len() == 1 {
        // base case: min of single element is that element
    } else {
        lemma_min_of_sequence_properties(s.skip(1));
        // inductive case follows from definition
    }
}

proof fn lemma_min_in_sequence(s: Seq<int>)
    requires s.len() > 0
    ensures exists|i: int| 0 <= i < s.len() && s[i] == min_of_sequence(s)
    decreases s.len()
{
    if s.len() == 1 {
        // base case
    } else {
        lemma_min_in_sequence(s.skip(1));
        // inductive case
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(lst: Vec<i8>) -> (result: i8)
    requires valid_input(lst@.map(|i: int, x: i8| x as int))
    ensures result as int == 2 + int_xor(lst@[2] as int, min_of_sequence(lst@.map(|i: int, x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let ghost int_seq = lst@.map(|i: int, x: i8| x as int);
    
    // Compute minimum iteratively
    let mut min_val = lst[0];
    let mut idx = 1;
    
    while idx < lst.len()
        invariant
            1 <= idx <= lst.len(),
            min_val as int == min_of_sequence(int_seq.take(idx as int)),
            1 <= min_val as int <= 32,
        decreases lst.len() - idx
    {
        if lst[idx] < min_val {
            min_val = lst[idx];
        }
        idx += 1;
    }
    
    proof {
        assert(int_seq.take(lst.len() as int) == int_seq);
    }
    
    let third_element = lst[2];
    let xor_result = (third_element as u32) ^ (min_val as u32);
    let final_result = 2 + (xor_result as i8);
    
    final_result
}
// </vc-code>


}

fn main() {}