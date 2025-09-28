use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn double_array_elements_lemma(s: Seq<i32>, j: int)
    requires
        0 <= j <= s.len(),
        forall|i: int| 0 <= i < j ==> s[i] == 2 * s[i]
    ensures
        forall|i: int| 0 <= i < j ==> s[i] == 2 * s[i]
{
}

proof fn preserve_old_values(s_old: Seq<i32>, s_new: Seq<i32>, j: int)
    requires
        0 <= j <= s_old.len(),
        s_old.len() == s_new.len(),
        forall|i: int| j <= i < s_old.len() ==> s_new[i] == s_old[i]
    ensures
        forall|i: int| j <= i < s_old.len() ==> s_new[i] == s_old[i]
{
}
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s[i] == 2 * old(s)[i]
// </vc-spec>
// <vc-code>
{
    let old_s = s.view();
    let len = s.len();
    let mut j: usize = 0;
    
    while j < len
        invariant
            j <= len,
            s.view().len() == old_s.len(),
            forall|i: int| 0 <= i < j as int ==> s.view()[i] == 2 * old_s[i],
            forall|i: int| j as int <= i < len as int ==> s.view()[i] == old_s[i]
    {
        let old_val = s[j];
        s[j] = 2 * old_val;
        
        proof {
            double_array_elements_lemma(s.view(), j as int);
            preserve_old_values(old_s, s.view(), (j + 1) as int);
        }
        
        j = j + 1;
    }
    
    proof {
        assert forall|i: int| 0 <= i < old_s.len() implies s.view()[i] == 2 * old_s[i] by {
            if i < len as int {
                assert(s.view()[i] == 2 * old_s[i]);
            }
        };
    }
}
// </vc-code>

fn main() {
}

}