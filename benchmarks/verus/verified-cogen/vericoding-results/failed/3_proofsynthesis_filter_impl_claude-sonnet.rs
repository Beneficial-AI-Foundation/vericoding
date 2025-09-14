// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): strengthened lemma with proper subrange properties */
proof fn filter_extension_lemma(s: Seq<u64>, elem: u64, i: int)
    requires
        i >= 0,
        i < s.len(),
        s[i] == elem,
    ensures
        elem % 3 == 0 ==> s.subrange(0, i + 1).filter(|k: u64| k % 3 == 0) == s.subrange(0, i).filter(|k: u64| k % 3 == 0).push(elem),
        elem % 3 != 0 ==> s.subrange(0, i + 1).filter(|k: u64| k % 3 == 0) == s.subrange(0, i).filter(|k: u64| k % 3 == 0),
{
    let prefix = s.subrange(0, i);
    let extended = s.subrange(0, i + 1);
    assert(extended == prefix.push(elem));
    
    if elem % 3 == 0 {
        assert(extended.filter(|k: u64| k % 3 == 0) == prefix.filter(|k: u64| k % 3 == 0).push(elem));
    } else {
        assert(extended.filter(|k: u64| k % 3 == 0) == prefix.filter(|k: u64| k % 3 == 0));
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
    /* code modified by LLM (iteration 5): fixed invariant and added proper proof structure */
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            y@ == x@.subrange(0, i as int).filter(|k: u64| k % 3 == 0),
        decreases x.len() - i
    {
        proof {
            filter_extension_lemma(x@, x@[i as int], i as int);
        }
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        i += 1;
    }
    proof {
        assert(i == x.len());
        assert(x@.subrange(0, i as int) == x@);
    }
}
// </vc-code>

}
fn main() {}