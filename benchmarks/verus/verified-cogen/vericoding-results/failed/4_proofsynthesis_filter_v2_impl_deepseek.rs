// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed decreases clause syntax and added proper proof helper */
proof fn filter_lemma(s: Seq<u64>, i: int) 
    ensures 
        s.filter(|k: u64| k % 3 == 0) == s.take(i).filter(|k: u64| k % 3 == 0).add(s.drop(i).filter(|k: u64| k % 3 == 0)),
    decreases if i < s.len() { s.len() - i } else { 0 },
{
    if i < s.len() as int {
        filter_lemma(s, i + 1);
    }
}

spec fn usize_to_int(i: usize) -> int {
    i as int
}
// </vc-helpers>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)

    requires 
        old(y).len() == 0,

    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop invariant and proof usage */
{
    let mut i: usize = 0;
    while i < x.len()
        invariant 
            y@ == x@.take(usize_to_int(i)).filter(|k: u64| k % 3 == 0),
            i <= x.len(),
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        filter_lemma(x@, usize_to_int(i));
        i += 1;
    }
}
// </vc-code>

}
fn main() {}