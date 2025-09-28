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
/* helper modified by LLM (iteration 2): fix nat/int usage in exec code */
exec fn compute_total_chars(lst: &Vec<Vec<char>>) -> (total: usize)
    ensures total == total_chars(lst@.map_values(|v: Vec<char>| v@))
{
    let mut total = 0;
    let mut i = 0;
    while i < lst.len()
        invariant 0 <= i <= lst.len(),
            total == total_chars( (lst@.take(i as int)).map_values(|v: Vec<char>| v@) )
        decreases lst.len() - i
    {
        total += lst[i].len();
        i += 1;
    }
    total
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
/* code modified by LLM (iteration 2): fix nat/int usage in exec code */
{
    let total1 = compute_total_chars(&lst1);
    let total2 = compute_total_chars(&lst2);
    if total1 <= total2 {
        lst1
    } else {
        lst2
    }
}
// </vc-code>


}

fn main() {}