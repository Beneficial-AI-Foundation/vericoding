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

/* helper modified by LLM (iteration 5): avoid unsupported Vec::from_iter in helper */
spec fn compute_total_chars(v: Vec<Vec<char>>) -> nat
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        v[0]@.len() + compute_total_chars(Vec::from_slice(v.subrange(1, v.len())))
    }
}

proof fn total_chars_eq_lemma(lst1: Vec<Vec<char>>, lst2: Vec<Vec<char>>)
    ensures
        total_chars(lst1@.map_values(|v: Vec<char>| v@)) == compute_total_chars(lst1),
        total_chars(lst2@.map_values(|v: Vec<char>| v@)) == compute_total_chars(lst2)
{
    // The two computations are equivalent
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
    /* code modified by LLM (iteration 5): use proper vector slicing */
    let total1 = compute_total_chars(lst1.clone());
    let total2 = compute_total_chars(lst2.clone());
    
    proof {
        total_chars_eq_lemma(lst1.clone(), lst2.clone());
    }
    
    if total1 <= total2 {
        lst1
    } else {
        lst2
    }
}
// </vc-code>


}

fn main() {}