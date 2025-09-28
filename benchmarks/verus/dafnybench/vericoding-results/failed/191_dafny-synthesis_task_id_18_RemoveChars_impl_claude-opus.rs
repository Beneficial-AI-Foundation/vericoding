use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
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
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < s1.len()
        invariant
            i <= s1.len(),
            result@.len() <= i,
            forall|j: int| 0 <= j < result@.len() ==> s1.contains(result@[j]) && !s2.contains(result@[j]),
            forall|j: int| 0 <= j < i ==> s2.contains(s1[j]) || result@.contains(s1[j]),
    {
        let c = s1[i as int];
        if !s2.contains(c) {
            result.push(c);
            proof {
                assert(result@.len() > 0);
                assert(result@[result@.len() - 1] == s1[i as int]);
                assert(s1.contains(s1[i as int]));
                assert(!s2.contains(s1[i as int]));
                assert(result@.contains(s1[i as int]));
            }
        } else {
            proof {
                assert(s2.contains(s1[i as int]));
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(i == s1.len());
        assert(forall|j: int| 0 <= j < s1.len() ==> s2.contains(s1[j]) || result@.contains(s1[j]));
    }
    
    result@
}
// </vc-code>

fn main() {
}

}