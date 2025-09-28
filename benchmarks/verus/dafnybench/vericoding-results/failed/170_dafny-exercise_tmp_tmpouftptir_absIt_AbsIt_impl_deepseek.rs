use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn abs_lemma(v: Seq<i32>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        if v[i] < 0 { -v[i] >= 0 } else { v[i] >= 0 }
{
}

proof fn preserves_length_lemma(v1: Seq<i32>, v2: Seq<i32>)
    requires
        v1.len() == v2.len(),
    ensures
        v1.len() == v2.len()
{
}

proof fn element_abs_lemma(old_v: Seq<i32>, new_v: Seq<i32>, i: int)
    requires
        0 <= i < old_v.len(),
        if old_v[i] < 0 { new_v[i] == -old_v[i] } else { new_v[i] == old_v[i] },
    ensures
        if old_v[i] < 0 { new_v[i] == -old_v[i] } else { new_v[i] == old_v[i] }
{
}
// </vc-helpers>

// <vc-spec>
fn abs_it(s: &mut Vec<i32>)
    ensures
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if old(s)[i] < 0 { s[i] == -old(s)[i] } else { s[i] == old(s)[i] }
// </vc-spec>
// <vc-code>
{
    let old_s = s@;
    let mut index: usize = 0;
    while index < s.len()
        invariant
            index <= s.len(),
            s@.len() == old_s.len(),
            forall|j: int| 0 <= j < index ==> 
                if old_s[j] < 0 { s@[j] == -old_s[j] } else { s@[j] == old_s[j] },
            forall|j: int| index <= j < s@.len() ==> s@[j] == old_s[j],
    {
        if s[index] < 0 {
            proof { abs_lemma(old_s, index as int); }
            s[index] = -s[index];
            proof { element_abs_lemma(old_s, s@, index as int); }
        }
        index = index + 1;
    }
    proof { preserves_length_lemma(old_s, s@); }
}
// </vc-code>

fn main() {}

}