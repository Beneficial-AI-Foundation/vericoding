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
/* helper modified by LLM (iteration 5): compute minimum using tracked ghost sequence and maintain invariant */
fn compute_min_vec(v: &Vec<i8>) -> i8
    requires
        v.len() >= 1,
    ensures
        ret as int == min_of_sequence(v@.map(|i: int, x: i8| x as int)),
{
    let s: Seq<int> = tracked (v@.map(|i: int, x: i8| x as int));
    let n: int = v.len() as int;
    let mut i: usize = 1usize;
    let mut cur_min: i8 = v[0];
    while i < v.len()
        invariant
            1 <= (i as int) <= n,
            (cur_min as int) == min_of_sequence(s.slice(0, i as int)),
        decreases
            (v.len() as int) - (i as int)
    {
        let xi = v[i];
        if xi < cur_min {
            cur_min = xi;
        }
        i = i + 1;
    }
    cur_min
}

// </vc-helpers>

// <vc-spec>
fn solve(lst: Vec<i8>) -> (result: i8)
    requires valid_input(lst@.map(|i: int, x: i8| x as int))
    ensures result as int == 2 + int_xor(lst@[2] as int, min_of_sequence(lst@.map(|i: int, x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute runtime min, xor, and prove spec-level equality */
    let min = compute_min_vec(&lst);
    let a = lst[2];
    let xr: u32 = (a as u32) ^ (min as u32);
    let out_u32: u32 = 2u32 + xr;
    let result: i8 = out_u32 as i8;
    proof {
        assert((min as int) == min_of_sequence(lst@.map(|i: int, x: i8| x as int)));
        assert(valid_input(lst@.map(|i: int, x: i8| x as int)));
        assert(1 <= lst@[2] && lst@[2] <= 32);
        assert(1 <= min as int && min as int <= 32);
        assert((xr as int) == int_xor(lst@[2] as int, min_of_sequence(lst@.map(|i: int, x: i8| x as int))));
        assert((out_u32 as int) == 2 + (xr as int));
        assert((result as int) == (out_u32 as i8) as int);
        assert((result as int) == 2 + int_xor(lst@[2] as int, min_of_sequence(lst@.map(|i: int, x: i8| x as int))));
    }
    result
}

// </vc-code>


}

fn main() {}