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
/* helper modified by LLM (iteration 5): changed i to int for consistent types in specifications and added usize cast for vector access */
fn exec_min_of_sequence(lst: &Vec<i8>) -> (min_val: i8)
    requires
        5 <= lst@.len() <= 10,
        forall|i: int| 0 <= i < lst@.len() ==> lst@[i] >= 1 && lst@[i] <= 32
    ensures
        min_val as int == min_of_sequence(lst@.map_values(|x: i8| x as int))
{
    let mut min_val = lst[0];
    let mut i = 1 as int;
    while i < lst.len() as int
        invariant
            1 <= i <= lst.len() as int,
            min_val as int == min_of_sequence(lst@.take(i).map_values(|x: i8| x as int))
        decreases lst.len() as int - i
    {
        if lst[i as usize] < min_val {
            min_val = lst[i as usize];
        }
        i += 1;
    }
    min_val
}
// </vc-helpers>

// <vc-spec>
fn solve(lst: Vec<i8>) -> (result: i8)
    requires valid_input(lst@.map(|i: int, x: i8| x as int))
    ensures result as int == 2 + int_xor(lst@[2] as int, min_of_sequence(lst@.map(|i: int, x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute computation in int to directly match spec expression */
    let min_s = exec_min_of_sequence(&lst);
    let min_as_int = min_s as int;
    let elem2 = lst@[2];
    let elem2_as_int = elem2 as int;
    let xor_u32 = elem2_as_int as u32 ^ min_as_int as u32;
    let xor_val = xor_u32 as int;
    let result_int = 2 + xor_val;
    let result = result_int as i8;
    result
}
// </vc-code>


}

fn main() {}