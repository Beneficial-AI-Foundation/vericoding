use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_char(s: Seq<char>, c: char) -> bool {
    exists|i: int| 0 <= i < s.len() && s@[i] == c
}

proof fn lemma_preserve_chars(s1: Seq<char>, s2: Seq<char>, v: Seq<char>)
    requires
        forall|i: int| 0 <= i < v.len() ==> contains_char(s1, v@[i]) && !contains_char(s2, v@[i]),
        forall|i: int| 0 <= i < s1.len() ==> contains_char(s2, s1@[i]) || contains_char(v, s1@[i]),
    ensures
        v.len() <= s1.len()
{
}

proof fn lemma_contains_equivalence(s: Seq<char>, c: char)
    ensures
        s.contains(c) <==> contains_char(s, c)
{
    assert(s.contains(c) == exists|i: int| 0 <= i < s.len() && s@[i] == c);
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
    let mut i: int = 0;
    
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> contains_char(s1, result@[j]) && !contains_char(s2, result@[j]),
            forall|j: int| 0 <= j < i ==> contains_char(s2, s1@[j]) || contains_char(result, s1@[j]),
    {
        if !contains_char(s2, s1@[i]) {
            result = result.push(s1@[i]);
        }
        i = i + 1;
    }
    
    proof {
        lemma_preserve_chars(s1, s2, result);
        assert(forall|i: int| 0 <= i < result.len() ==> s1.contains(result@[i]) && !s2.contains(result@[i]));
        assert(forall|i: int| 0 <= i < s1.len() ==> s2.contains(s1@[i]) || result.contains(s1@[i]));
    }
    
    result
}
// </vc-code>

fn main() {
}

}