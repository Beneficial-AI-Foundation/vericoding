use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// Provide no-op helper section to keep file structure. No additional helpers needed.
 
// </vc-helpers>
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
    let mut vec = Vec::<char>::new();
    let mut i: usize = 0usize;
    while i < s1.len() {
        invariant(i <= s1.len());
        invariant(vec.len() <= s1.len());
        invariant(forall |j: usize| j < vec.len() ==> !s2.contains(*vec[j]));
        invariant(forall |j: usize| j < vec.len() ==> s1.contains(*vec[j]));
        invariant(forall |k: usize| k < i ==> s2.contains(s1@k) || vec.contains(&s1@k));
        if !s2.contains(s1@i) {
            vec.push(s1@i);
            assert(vec.contains(&s1@i));
            assert(!s2.contains(s1@i));
        }
        i = i + 1;
    }
    let v = vec.to_seq();
    proof {
        assert(forall |k: int| 0 <= k && k < s1.len() as int ==> s2.contains(s1@k) || vec.contains(&s1@k));
        assert(forall |j: int| 0 <= j && j < vec.len() as int ==> s1.contains(*vec[j]));
        assert(forall |j: int| 0 <= j && j < vec.len() as int ==> !s2.contains(*vec[j]));
        assert(v.len() == vec.len());
        assert(forall |j: int| 0 <= j && j < v.len() ==> s1.contains(v@j));
        assert(forall |j: int| 0 <= j && j < v.len() ==> !s2.contains(v@j));
        assert(forall |k: int| 0 <= k && k < s1.len() as int ==> s2.contains(s1@k) || v.contains(s1@k));
    }
    v
}
// </vc-code>

fn main() {
}

}