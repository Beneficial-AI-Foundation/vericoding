// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn total_chars(lst: Seq<Seq<char>>) -> nat
    decreases lst.len()
{
    if lst.len() == 0 {
        0
    } else {
        lst[0].len() + total_chars(lst.subrange(1, lst.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation errors by using usize for exec variables and adjusting spec to match exec accumulation */
fn calc_total(vv: &Vec<Vec<char>>) -> (total: usize)
    ensures
        total_chars(vv@.map_values(|v: Vec<char>| v@)) <= usize::MAX as int,
        total as int == total_chars(vv@.map_values(|v: Vec<char>| v@))
{
    let mut acc: usize = 0;
    let mut i: usize = 0;
    while i < vv.len()
        invariant
            0 <= i as int <= vv@.len(),
            acc as int == total_chars(vv@.subrange(0, i as int).map_values(|v: Vec<char>| v@))
        decreases vv@.len() - i as int
    {
        acc += vv[i].len();
        proof {
            assert(total_chars(vv@.subrange(0, (i + 1) as int).map_values(|v: Vec<char>| v@)) == total_chars(vv@.subrange(0, i as int).map_values(|v: Vec<char>| v@)) + vv@[i].len());
            assert(acc as int == total_chars(vv@.subrange(0, (i + 1) as int).map_values(|v: Vec<char>| v@)));
        }
        i += 1;
    }
    proof {
        assert(i as int == vv@.len());
        if i == vv.len() {
            assert(total_chars(vv@.subrange(0, vv@.len()).map_values(|v: Vec<char>| v@)) == total_chars(vv@.map_values(|v| v@)));
        }
        assert(total_chars(vv@.map_values(|v: Vec<char>| v@)) <= usize::MAX as int);
        assert(acc as int == total_chars(vv@.map_values(|v| v@)));
    }
    acc
}
// </vc-helpers>

// <vc-spec>
fn total_match(lst1: Vec<Vec<char>>, lst2: Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    ensures 
        result@ == lst1@ || result@ == lst2@,
        total_chars(lst1@.map_values(|v: Vec<char>| v@)) <= total_chars(lst2@.map_values(|v: Vec<char>| v@)) ==> result@ == lst1@,
        total_chars(lst1@.map_values(|v: Vec<char>| v@)) > total_chars(lst2@.map_values(|v: Vec<char>| v@)) ==> result@ == lst2@
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed as helper fixes address issues */
    let total1 = calc_total(&lst1);
    let total2 = calc_total(&lst2);
    if total1 <= total2 {
        lst1.clone()
    } else {
        lst2.clone()
    }
}
// </vc-code>


}

fn main() {}