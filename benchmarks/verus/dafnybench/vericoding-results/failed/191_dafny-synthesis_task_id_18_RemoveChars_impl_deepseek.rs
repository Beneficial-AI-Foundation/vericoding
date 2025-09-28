use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_not(s: Seq<char>, c: char) -> bool {
    !s.contains(c)
}

proof fn lemma_seq_filter_properties(s1: Seq<char>, s2: Seq<char>)
    ensures
        forall|i: int| 0 <= i < s1.filter(|c| contains_not(s2, c)).len() ==> 
            s1.contains(s1.filter(|c| contains_not(s2, c))[i]) && contains_not(s2, s1.filter(|c| contains_not(s2, c))[i]),
        forall|i: int| 0 <= i < s1.len() ==> 
            !contains_not(s2, s1[i]) || s1.filter(|c| contains_not(s2, c)).contains(s1[i])
{
}
// </vc-helpers>

// <vc-spec>
fn remove_chars(s1: Seq<char>, s2: Seq<char>) -> (v: Seq<char>)
    ensures 
        v.len() <= s1.len(),
        forall|i: int| 0 <= i < v.len() ==> s1.contains(v[i]) && !s2.contains(v[i]),
        forall|i: int| 0 <= i < s1.len() ==> s2.contains(s1[i]) || v.contains(s1[i])
// </vc-spec>
// <vc-code>
{
    let mut result = Seq::<char>::empty();
    let mut idx: nat = 0;
    
    while idx < s1.len()
        invariant 
            0 <= idx <= s1.len(),
            result.len() <= s1.len(),
            forall|i: int| 0 <= i < result.len() ==> s1.contains(result[i]) && !s2.contains(result[i]),
            forall|i: int| 0 <= i < idx ==>
                !s2.contains(s1[i]) ==> result.contains(s1[i]),
            forall|c: char| result.contains(c) ==> !s2.contains(c)
    {
        let current_char = s1[idx];
        if !s2.contains(current_char) {
            proof {
                assert(s1.contains(current_char));
                assert(!s2.contains(current_char));
            }
            result = result.add(current_char);
        }
        proof {
            assert forall|i: int| 0 <= i < idx+1 implies 
                !s2.contains(s1[i]) ==> result.contains(s1[i]) by {
                if i == idx {
                    if !s2.contains(s1[i]) {
                        assert(result.contains(s1[i]));
                    }
                } else {
                }
            }
        }
        idx = idx + 1;
    }
    
    proof {
        lemma_seq_filter_properties(s1, s2);
        assert forall|i: int| 0 <= i < s1.len() implies s2.contains(s1[i]) || result.contains(s1[i]) by {
            if !s2.contains(s1[i]) {
                assert(result.contains(s1[i]));
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}