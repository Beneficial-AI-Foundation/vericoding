use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains_char(s: Seq<char>, c: char) -> bool {
    // This helper is for demonstration purposes. 
    // `Seq::contains` is already built-in.
    // However, for more complex custom containments or predicates, 
    // a helper function like this might be necessary.
    // The given problem description doesn't strictly need this,
    // but it shows how a helper might be structured.
    // For this specific problem, we directly use `Seq::contains`.
    true
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
    let mut result_vec: Vec<char> = Vec::new();
    let s1_len: nat = s1.len();

    let mut i: int = 0;
    while i < s1_len as int
        invariant
            0 <= i <= s1_len,
            result_vec.len() as int <= i, // The length of result_vec cannot exceed the number of processed characters from s1
            forall|k: int| 0 <= k < result_vec.len() ==> s1.contains(result_vec@[k]),
            forall|k: int| 0 <= k < result_vec.len() ==> !s2.contains(result_vec@[k]),
            forall|k: int| 0 <= k < i ==> s2.contains(s1[k]) || (result_vec@).contains(s1[k]),
        decreases (s1_len as int) - i
    {
        let char_s1 = s1.index(i);

        if !s2.contains(char_s1) {
            result_vec.push(char_s1);
            proof {
                assert(s1.contains((result_vec@)[(result_vec.len() - 1) as int]));
                assert(!s2.contains((result_vec@)[(result_vec.len() - 1) as int]));
            }
        }
        i = i + 1;
    }

    let v = result_vec@;

    assert(v.len() <= s1.len()) by {
        assert(result_vec.len() as int <= i);
        assert(i == s1_len as int);
        assert(result_vec.len() as int <= s1_len as int);
    }

    assert forall|k: int| 0 <= k < v.len() implies s1.contains(v[k]) && !s2.contains(v[k]) by {
        assert(forall|j: int| 0 <= j < result_vec.len() ==> s1.contains((result_vec@)[j]));
        assert(forall|j: int| 0 <= j < result_vec.len() ==> !s2.contains((result_vec@)[j]));
    }

    assert forall|k: int| 0 <= k < s1.len() implies s2.contains(s1[k]) || v.contains(s1[k]) by {
        assert(forall|j: int| 0 <= j < s1_len as int ==> s2.contains(s1[j]) || (result_vec@).contains(s1[j]));
    }

    v
}
// </vc-code>

fn main() {
}

}