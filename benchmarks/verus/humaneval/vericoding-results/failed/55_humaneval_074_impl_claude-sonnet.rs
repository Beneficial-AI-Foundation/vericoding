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
/* helper modified by LLM (iteration 5): added spec function to convert Vec<Vec<char>> to Seq<Seq<char>> */
spec fn vec_to_seq_seq(lst: Vec<Vec<char>>) -> Seq<Seq<char>> {
    lst@.map_values(|v: Vec<char>| v@)
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
    /* code modified by LLM (iteration 5): use helper function to avoid closure compilation errors */
    let seq1 = vec_to_seq_seq(lst1);
    let seq2 = vec_to_seq_seq(lst2);
    
    let total1 = total_chars(seq1);
    let total2 = total_chars(seq2);
    
    if total1 <= total2 {
        lst1
    } else {
        lst2
    }
}
// </vc-code>


}

fn main() {}