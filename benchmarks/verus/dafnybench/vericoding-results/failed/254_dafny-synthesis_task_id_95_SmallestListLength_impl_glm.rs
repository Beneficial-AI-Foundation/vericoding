use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::external_body]
fn seq_index<T>(s: Seq<T>, i: int) -> (result: T)
    requires
        0 <= i < s.len(),
    ensures
        result == s[i],
{
    s[i]
}

proof fn lemma_min_len_exists(s: Seq<Seq<int>>, i: int, min_len: int)
    requires
        0 < i <= s.len(),
        forall|k: int| 0 <= k < i ==> min_len <= seq_index(s, k).len(),
        exists|k: int| 0 <= k < i && min_len == seq_index(s, k).len(),
        seq_index(s, i-1).len() >= min_len,
    ensures
        forall|k: int| 0 <= k < i ==> min_len <= seq_index(s, k).len(),
        exists|k: int| 0 <= k < i && min_len == seq_index(s, k).len(),
{
    if seq_index(s, i-1).len() == min_len {
        assert forall|k: int| 0 <= k < i implies min_len <= seq_index(s, k).len() by {
            if k != i-1 {
                assert(seq_index(s, k).len() >= min_len);
            }
        }
        assert(exists|k: int| 0 <= k < i && min_len == seq_index(s, k).len());
    } else {
        assert forall|k: int| 0 <= k < i implies min_len <= seq_index(s, k).len();
        assert(exists|k: int| 0 <= k < i && min_len == seq_index(s, k).len());
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_list_length(s: Seq<Seq<int>>) -> (v: int)
    requires
        s.len() > 0,
    ensures
        forall|i: int| 0 <= i < s.len() ==> v <= s[i].len(),
        exists|i: int| 0 <= i < s.len() && v == #[trigger] s[i].len(),
// </vc-spec>
// <vc-code>
{
    let mut min_len = s[0].len();
    let mut i = 1;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int| 0 <= k < i ==> min_len <= seq_index(s, k).len(),
            exists|k: int| 0 <= k < i && min_len == seq_index(s, k).len(),
    {
        let current_len = seq_index(s, i).len();
        if current_len < min_len {
            min_len = current_len;
            proof {
                assert forall|k: int| 0 <= k <= i implies min_len <= seq_index(s, k).len() by {
                    if k < i {
                        assert(seq_index(s, k).len() >= current_len);
                    }
                }
                assert(exists|k: int| 0 <= k <= i && min_len == seq_index(s, k).len());
            }
        } else {
            proof {
                lemma_min_len_exists(s, i + 1, min_len);
            }
        }
        i = i + 1;
    }
    min_len
}
// </vc-code>

fn main() {
}

}