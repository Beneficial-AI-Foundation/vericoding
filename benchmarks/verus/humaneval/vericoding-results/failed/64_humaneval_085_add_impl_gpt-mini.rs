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
/* helper modified by LLM (iteration 2): seq_of_vec converts Vec<i8> to Seq<int> */
spec fn seq_of_vec(v: Vec<i8>) -> Seq<int> {
    v@.map_values(|x: i8| x as int)
}

// </vc-helpers>

// <vc-spec>
fn add(v: Vec<i8>) -> (r: i8)
    ensures r == sumc(v@.map_values(|x: i8| x as int), add_condition(v@.map_values(|x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): avoid creating Seq<int> at runtime; use spec expressions inline and maintain proof linking runtime sum to spec sumc */
    let n = v.len();
    let mut i: usize = 0;
    let mut sum: i8 = 0;
    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            (sum as int) == sumc(v@.map_values(|x: i8| x as int).subrange(0, i as int), add_condition(v@.map_values(|x: i8| x as int).subrange(0, i as int))),
        decreases n - i
    {
        if add_condition(v@.map_values(|x: i8| x as int))@[i as int] {
            sum = sum + v[i];
        }
        i += 1;
    }
    let r: i8 = sum;
    r
}

// </vc-code>


}

fn main() {}