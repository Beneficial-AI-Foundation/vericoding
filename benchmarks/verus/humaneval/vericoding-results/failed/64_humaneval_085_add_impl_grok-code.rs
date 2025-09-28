// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sumc(s: Seq<int>, p: Seq<bool>) -> int
    recommends s.len() == p.len()
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if p[0] { s[0] } else { 0 }) + sumc(s.subrange(1, s.len() as int), p.subrange(1, p.len() as int))
    }
}

spec fn add_condition(lst: Seq<int>) -> Seq<bool> {
    Seq::new(lst.len(), |i: int| i % 2 == 1 && lst[i] % 2 == 0)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(v: Vec<i8>) -> (r: i8)
    ensures r == sumc(v@.map_values(|x: i8| x as int), add_condition(v@.map_values(|x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error by using bit operations & 1 == 1 for odd index and & 1 == 0 for even value instead of casting to int */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum >= -128 && sum <= 127,
            sum as int == sumc(v@.map_values(|x: i8| x as int).subrange(0, i as int), add_condition(v@.map_values(|x: i8| x as int)).subrange(0, i as int))
        decreases v.len() - i
    {
        if (i & 1) == 1 && ((v[i] as i32) & 1) == 0 {
            sum += v[i] as i32;
        }
        i += 1;
    }
    sum as i8
}
// </vc-code>


}

fn main() {}