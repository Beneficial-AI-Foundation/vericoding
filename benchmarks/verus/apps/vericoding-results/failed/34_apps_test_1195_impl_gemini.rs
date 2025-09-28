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
/* helper modified by LLM (iteration 2): [refined logic and added postcondition] */
fn find_min(lst: &Vec<i8>) -> (min_val: i8)
    requires
        lst.len() > 0,
        forall |i: int| 0 <= i < lst@.len() ==> 1 <= lst@[i] <= 32,
    ensures
        min_val as int == min_of_sequence(lst@.map(|i, x| x as int)),
        exists |i: int| 0 <= i < lst@.len() && min_val == lst@[i],
{
    let mut min_val = lst[lst.len() - 1];
    let mut i: usize = lst.len() - 1;
    while i > 0
        invariant
            0 <= i < lst.len(),
            min_val as int == min_of_sequence(lst@.subrange(i as int, lst.len() as int).map(|_i, x| x as int)),
            exists |j: int| i <= j < lst.len() as int && min_val == lst@[j],
            forall|k: int| 0 <= k < lst@.len() ==> 1 <= lst@[k] <= 32,
        decreases i
    {
        i = i - 1;
        if lst[i] <= min_val {
            min_val = lst[i];
        }
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
/* code modified by LLM (iteration 2): [added assertions for overflow safety] */
{
    let min_val = find_min(&lst);
    let val2 = lst[2];

    assert(1 <= min_val <= 32);
    assert(1 <= val2 <= 32);
    assert((val2 ^ min_val) as int == int_xor(val2 as int, min_val as int));

    let result = 2i8 + (val2 ^ min_val);
    result
}
// </vc-code>


}

fn main() {}