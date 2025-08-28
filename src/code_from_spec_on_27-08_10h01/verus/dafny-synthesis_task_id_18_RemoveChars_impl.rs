use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_char_in_seq(s: Seq<char>, c: char) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}

proof fn contains_equivalent(s: Seq<char>, c: char)
    ensures contains_char_in_seq(s, c) == s.contains(c)
{
}

proof fn push_preserves_contains<T>(s: Seq<T>, elem: T, x: T)
    ensures s.push(elem).contains(x) == (s.contains(x) || x == elem)
{
}

proof fn push_len<T>(s: Seq<T>, elem: T)
    ensures s.push(elem).len() == s.len() + 1
{
}

proof fn push_indexing<T>(s: Seq<T>, elem: T, i: int)
    requires 0 <= i < s.len()
    ensures s.push(elem)[i] == s[i]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn remove_chars(s1: Seq<char>, s2: Seq<char>) -> (v: Seq<char>)
    ensures 
        v.len() <= s1.len(),
        forall|i: int| 0 <= i < v.len() ==> s1.contains(v[i]) && !s2.contains(v[i]),
        forall|i: int| 0 <= i < s1.len() ==> s2.contains(s1[i]) || v.contains(s1[i])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result: Seq<char> = Seq::empty();
    let mut idx: nat = 0;
    
    while idx < s1.len()
        invariant
            0 <= idx <= s1.len(),
            result.len() <= idx,
            forall|i: int| 0 <= i < result.len() ==> s1.contains(result[i]) && !s2.contains(result[i]),
            forall|i: int| 0 <= i < idx ==> s2.contains(s1@[i]) || result.contains(s1@[i])
    {
        let ch = s1@[idx as int];
        if !s2.contains(ch) {
            result = result.push(ch);
            proof {
                push_preserves_contains(result.drop_last(), ch, ch);
                assert(result.contains(ch));
                
                let old_result = result.drop_last();
                assert(forall|i: int| 0 <= i < old_result.len() ==> s1.contains(old_result[i]) && !s2.contains(old_result[i]));
                assert(s1.contains(ch) && !s2.contains(ch));
                assert(forall|i: int| 0 <= i < result.len() ==> s1.contains(result[i]) && !s2.contains(result[i]));
                
                assert(forall|i: int| 0 <= i < idx ==> s2.contains(s1@[i]) || old_result.contains(s1@[i]));
                push_preserves_contains(old_result, ch, s1@[idx as int]);
                assert(result.contains(s1@[idx as int]));
                assert(forall|i: int| 0 <= i <= idx ==> s2.contains(s1@[i]) || result.contains(s1@[i]));
            }
        } else {
            proof {
                assert(s2.contains(s1@[idx as int]));
                assert(forall|i: int| 0 <= i <= idx ==> s2.contains(s1@[i]) || result.contains(s1@[i]));
            }
        }
        idx = idx + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}