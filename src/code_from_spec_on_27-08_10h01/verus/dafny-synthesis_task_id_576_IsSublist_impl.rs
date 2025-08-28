use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn seqs_equal(s1: Seq<int>, s2: Seq<int>) -> bool {
    s1.len() == s2.len() && forall|k: int| 0 <= k < s1.len() ==> s1[k] == s2[k]
}

proof fn subrange_equality_lemma(sub: Seq<int>, main: Seq<int>, i: int)
    requires
        0 <= i <= main.len() - sub.len(),
        seqs_equal(sub, main.subrange(i, i + sub.len()))
    ensures
        sub =~= main.subrange(i, i + sub.len())
{
    assert(sub.len() == main.subrange(i, i + sub.len()).len());
    assert(forall|k: int| 0 <= k < sub.len() ==> sub[k] == main.subrange(i, i + sub.len())[k]);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == exists|i: int, j: int| 0 <= i <= main.len() - sub.len() && j == i + sub.len() && sub =~= #[trigger] main.subrange(i, j)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if sub.len() == 0 {
        return true;
    }
    
    if sub.len() > main.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= (main.len() - sub.len()) as usize
        invariant
            0 <= i <= main.len() - sub.len() + 1,
            forall|k: int| 0 <= k < i ==> !seqs_equal(sub, main.subrange(k, k + sub.len()))
    {
        let mut j: usize = 0;
        let mut matches = true;
        
        while j < sub.len() as usize
            invariant
                0 <= j <= sub.len(),
                matches == (forall|k: int| 0 <= k < j ==> sub[k] == main[i as int + k])
        {
            if sub[j] != main[i + j] {
                matches = false;
                break;
            }
            j += 1;
        }
        
        if matches {
            proof {
                assert(seqs_equal(sub, main.subrange(i as int, i as int + sub.len())));
                subrange_equality_lemma(sub, main, i as int);
            }
            return true;
        }
        
        i += 1;
    }
    
    false
}
// </vc-code>

fn main() {
}

}