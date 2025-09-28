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
/* code modified by LLM (iteration 5): Fixed indexing error by using `v[i]` instead of `v@[i]` for runtime access. */
{
    let mut total: i8 = 0;
    let mut i: usize = 0;

    while i < v.len()
        invariant
            0 <= i,
            i <= v.len(),
            total as int == sumc(v@.subrange(0, i as int).map_values(|x: i8| x as int), add_condition(v@.subrange(0, i as int).map_values(|x: i8| x as int))),
            v.len() == v@.len(),
        decreases v.len() - i
    {
        if (i as int) % 2 == 1 && v[i] % 2 == 0 {
            total = total + v[i];
        }
        i = i + 1;
    }
    proof {
        assert(total as int == sumc(v@.map_values(|x: i8| x as int), add_condition(v@.map_values(|x: i8| x as int))));
    }
    total
}
// </vc-code>


}

fn main() {}