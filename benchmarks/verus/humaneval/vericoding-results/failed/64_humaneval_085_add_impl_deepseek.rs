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


proof fn sumc_equals_sumc_in_range(s: Seq<int>, p: Seq<bool>, start: nat, end: nat)
    requires start <= end <= s.len(), s.len() == p.len()
    ensures sumc(s.subrange(start, end), p.subrange(start, end)) == sumc_in_range(s, p, start, end)
    decreases end - start
{
    if start < end {
        sumc_equals_sumc_in_range(s, p, (start + 1) as nat, end);
    }
}

spec fn is_odd_index_even_value(i: int, v: i8) -> bool {
    i % 2 == 1 && v as int % 2 == 0
}

spec fn add_condition_new(lst: Seq<int>) -> Seq<bool> {
    Seq::new(lst.len(), |i: int| i % 2 == 1 && lst[i] % 2 == 0)
}

spec fn sumc_in_range(s: Seq<int>, p: Seq<bool>, start: nat, end: nat) -> int
    requires start <= end <= s.len(), s.len() == p.len()
    decreases end - start
{
    if start >= end {
        0
    } else {
        (if p[start] { s[start] } else { 0 }) + sumc_in_range(s, p, (start + 1) as nat, end)
    }
}
/* helper modified by LLM (iteration 5): Changed int to nat parameters to avoid compilation errors */

// </vc-helpers>

// <vc-spec>
fn add(v: Vec<i8>) -> (r: i8)
    ensures r == sumc(v@.map_values(|x: i8| x as int), add_condition(v@.map_values(|x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type casting from nat to avoid int/nat errors */
    let mut result: i8 = 0;
    let mut i: usize = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            result as int == sumc_in_range(v@.map_values(|x: i8| x as int), 
                            add_condition_new(v@.map_values(|x: i8| x as int)), 0, i),
        decreases v.len() - i
    {
        let idx = i;
        let val = v[i] as int;
        let condition = idx % 2 == 1 && val % 2 == 0;
        
        if condition {
            result = (result as i16 + v[i] as i16) as i8;
        }
        i += 1;
    }
    
    proof {
        sumc_equals_sumc_in_range(v@.map_values(|x: i8| x as int), 
            add_condition_new(v@.map_values(|x: i8| x as int)), 0, v.len());
    }
    
    result
}
// </vc-code>


}

fn main() {}