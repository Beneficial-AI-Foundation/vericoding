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
/* helper modified by LLM (iteration 5): [add explicit type annotation to closure] */
fn total_chars_vec(lst: &Vec<Vec<char>>) -> (result: nat)
    ensures result == total_chars(lst@.map_values(|v: Vec<char>| v@))
{
    total_chars(lst@.map_values(|v| v@))
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
/* code modified by LLM (iteration 5): [no changes needed from prior successful fix] */
{
    if total_chars_vec(&lst1) <= total_chars_vec(&lst2) {
        lst1
    } else {
        lst2
    }
}
// </vc-code>


}

fn main() {}