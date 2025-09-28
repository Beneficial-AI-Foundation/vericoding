// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

proof fn filter_lemma(s: Seq<u64>, i: int) 
    ensures 
        i >= 0 && i <= s.len() ==> 
        s.filter(|k: u64| k % 3 == 0) == 
        s.subrange(0, i as int).filter(|k: u64| k % 3 == 0) +
        s.subrange(i, s.len() as int).filter(|k: u64| k % 3 == 0)
{
    if i >= 0 && i <= s.len() {
        s.lemma_seq_filter_split(i as nat);
    }
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
{
    /* code modified by LLM (iteration 5): Fixed lemma name from lemma_filter_split to lemma_seq_filter_split */
    let mut i: usize = 0;
    while i < x.len()
        invariant 
            i <= x.len(),
            y@ == x@.subrange(0, i as int).filter(|k: u64| k % 3 == 0),
            y.len() == x@.subrange(0, i as int).filter(|k: u64| k % 3 == 0).len() as usize,
        decreases x.len() - i,
    {
        let current = x[i];
        if current % 3 == 0 {
            y.push(current);
            proof {
                filter_lemma(x@, i as int + 1);
            }
        } else {
            proof {
                filter_lemma(x@, i as int + 1);
            }
        }
        i += 1;
    }
}
// </vc-code>

}
fn main() {}