use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::proof]
fn lemma_min_property(s: Seq<Seq<int>>, min_idx: int)
    requires
        0 <= min_idx && min_idx < s.len(),
        forall|i: int| 0 <= i < s.len() ==> s[min_idx].len() <= s[i].len(),
    ensures
        forall|i: int| 0 <= i < s.len() ==> s[min_idx].len() <= s[i].len(),
        exists|i: int| 0 <= i < s.len() && s[min_idx].len() == #[trigger] s[i].len(),
{
}
// </vc-helpers>

// <vc-spec>
fn smallest_list_length(s: Seq<Seq<int>>) -> (v: int)
    requires
        s.len() > 0,
    ensures
        forall|i: int| 0 <= i < s.len() ==> v <= s[i].len(),
        exists|i: int| 0 <= i < s.len() && v == #[trigger] s[i].len(),
// </vc-spec>
// <vc-code>
{
    let mut min_len = (s@[0].len() as usize);
    let mut min_idx: usize = 0;
    
    proof {
        assert(min_len as int == s[0].len());
        assert(forall|i: int| 0 <= i < 1 ==> min_len as int <= s[i].len()) by {
            assert(0 <= 0 < 1);
            assert(min_len as int <= min_len as int);
        }
    }
    
    for i in 0..(s.len() as usize)
        invariant
            0 <= min_idx as int,
            min_idx as int < s.len(),
            min_len as int == s[min_idx as int].len(),
            forall|j: int| 0 <= j < (i as int) ==> min_len as int <= s[j].len(),
            0 <= (i as int),
            (i as int) <= s.len(),
    {
        if s@[i].len() < (min_len as int) {
            min_len = s@[i].len() as usize;
            min_idx = i;
        }
        assert(min_len as int <= s@[i].len());
    }
    
    proof {
        assert(min_len as int == s[min_idx as int].len());
        assert(forall|i: int| 0 <= i < s.len() ==> min_len as int <= s[i].len());
        assert(exists|i: int| 0 <= i < s.len() && min_len as int == #[trigger] s[i].len()) by {
            assert(0 <= min_idx as int);
            assert(min_idx as int < s.len());
            assert(min_len as int == s[min_idx as int].len());
        };
    }
    
    min_len as int
}
// </vc-code>

fn main() {
}

}