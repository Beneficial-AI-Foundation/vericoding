use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_subseq_contains<T>(s: Seq<T>, sub: Seq<T>, x: T)
    requires
        forall|i: int| 0 <= i < sub.len() ==> s.contains(sub[i]),
        sub.contains(x)
    ensures
        s.contains(x)
{
}

proof fn lemma_push_contains<T>(s: Seq<T>, x: T, y: T)
    ensures
        s.push(x).contains(y) <==> (s.contains(y) || y == x)
{
}

proof fn lemma_push_len<T>(s: Seq<T>, x: T)
    ensures
        s.push(x).len() == s.len() + 1
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
    let mut i: nat = 0nat;
    
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> s1.contains(result[j]) && !s2.contains(result[j]),
            forall|j: int| 0 <= j < i ==> s2.contains(s1[j]) || result.contains(s1[j])
    {
        let ch = s1[i];
        if !s2.contains(ch) {
            result = result.push(ch);
            proof {
                lemma_push_len(result.drop_last(), ch);
                assert(result.len() <= i + 1);
                
                // Prove first postcondition for new element
                assert(s1.contains(ch));
                assert(!s2.contains(ch));
                
                // Prove first postcondition is preserved
                assert(forall|j: int| 0 <= j < result.len() ==> #[trigger] s1.contains(result[j]) && !s2.contains(result[j])) by {
                    assert(forall|j: int| 0 <= j < result.drop_last().len() ==> s1.contains(result.drop_last()[j]) && !s2.contains(result.drop_last()[j]));
                    lemma_push_contains(result.drop_last(), ch, ch);
                }
                
                // Prove third postcondition is preserved
                assert(forall|j: int| 0 <= j < i + 1 ==> s2.contains(s1[j]) || result.contains(s1[j])) by {
                    assert(forall|j: int| 0 <= j < i ==> s2.contains(s1[j]) || result.drop_last().contains(s1[j]));
                    assert(result.contains(ch));
                }
            }
        }
        i = i + 1nat;
    }
    
    proof {
        assert(result.len() <= s1.len());
        assert(forall|j: int| 0 <= j < result.len() ==> s1.contains(result[j]) && !s2.contains(result[j]));
        assert(forall|j: int| 0 <= j < s1.len() ==> s2.contains(s1[j]) || result.contains(s1[j]));
    }
    
    result
}
// </vc-code>

fn main() {
}

}