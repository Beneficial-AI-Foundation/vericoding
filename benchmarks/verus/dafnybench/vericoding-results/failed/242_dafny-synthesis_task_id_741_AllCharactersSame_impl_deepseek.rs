use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn all_same_property(s: Seq<u8>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        s[i] == s[j],
    ensures
        s[i] == s[j]
{
}

proof fn exists_different_property(s: Seq<u8>, i: int, j: int)
    requires
        i != j,
        0 <= i < s.len(),
        0 <= j < s.len(),
        s[i] != s[j],
    ensures
        exists|ii: int, jj: int| 0 <= ii < s.len() && 0 <= jj < s.len() && ii != jj && s[ii] != s[jj]
{
    assert(0 <= i < s.len());
    assert(0 <= j < s.len());
    assert(i != j);
    assert(s[i] != s[j]);
}
// </vc-helpers>

// <vc-spec>
fn all_characters_same(s: Seq<u8>) -> (result: bool)
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j])
// </vc-spec>
// <vc-code>
{
    if s.len() == 0 {
        true
    } else {
        let first = s[0];
        let mut all_same = true;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                all_same ==> (forall|j: int| 0 <= j < i ==> s[j] == first),
                !all_same ==> (exists|k: int, l: int| 0 <= k < i && 0 <= l < i && k != l && s[k] != s[l])
        {
            if s[i] != first {
                all_same = false;
                break;
            }
            i = i + 1;
        }
        if all_same {
            proof {
                let mut j: int = 0;
                while j < s.len()
                    invariant
                        0 <= j <= s.len(),
                        forall|k: int| 0 <= k < j ==> s[k] == first
                {
                    if j < s.len() {
                        assert(s[j] == first);
                    }
                    j = j + 1;
                }
            }
            true
        } else {
            proof {
                assert(i > 0);
                let k: int = 0;
                let l: int = (i - 1) as int;
                assert(0 <= k < s.len());
                assert(0 <= l < s.len());
                assert(k != l);
                assert(s[k] == first);
                assert(s[l] != first);
                assert(s[k] != s[l]);
                exists_different_property(s, k, l);
            }
            false
        }
    }
}
// </vc-code>

fn main() {
}

}