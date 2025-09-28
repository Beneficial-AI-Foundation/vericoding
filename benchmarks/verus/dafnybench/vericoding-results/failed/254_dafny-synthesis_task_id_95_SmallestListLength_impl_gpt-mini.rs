use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let mut i: nat = 1;
    let mut min_len: nat = s@[0].len();
    let mut min_idx: nat = 0;
    while i < s.len()
        invariant i <= s.len();
        invariant (forall |j: nat| j < i ==> min_len <= s@[j].len());
        invariant min_idx < i;
        invariant min_len == s@[min_idx].len();
        decreases s.len() - i;
    {
        let cur: nat = s@[i].len();
        let old_min = min_len;
        let old_min_idx = min_idx;
        if cur < old_min {
            min_len = cur;
            min_idx = i;
            proof {
                // cur < old_min implies cur <= old_min
                assert(cur <= old_min);
                // from invariant: for all j < i, old_min <= s@[j].len()
                assert((forall |j: nat| j < i ==> old_min <= s@[j].len()));
                // combine to get: for all j < i, cur <= s@[j].len()
                assert((forall |j: nat| j < i ==> cur <= s@[j].len()));
                // min_len == cur and min_idx == i, so min_len == s@[min_idx].len()
                assert(min_len == s@[min_idx].len());
                // min_idx == i < i+1
                assert(min_idx < i + 1);
                // hence for all j < i+1, min_len <= s@[j].len()
                assert((forall |j: nat| j < i + 1 ==> min_len <= s@[j].len()));
            }
        } else {
            proof {
                // min_len and min_idx unchanged, relate them to old_min and old_min_idx
                assert(min_len == old_min);
                assert(min_idx == old_min_idx);
                // from invariant: for all j < i, old_min <= s@[j].len()
                assert((forall |j: nat| j < i ==> old_min <= s@[j].len()));
                // cur >= old_min
                assert(old_min <= cur);
                // for j < i, old_min <= s@[j].len(); for j == i, old_min <= cur == s@[i].len()
                assert((forall |j: nat| j < i + 1 ==> old_min <= s@[j].len()));
                // min_idx unchanged and less than i, so < i+1
                assert(old_min_idx < i + 1);
                // min_len unchanged equals s@[old_min_idx].len()
                assert(min_len == s@[old_min_idx].len());
            }
        }
        i = i + 1;
    }
    min_len as int
}
// </vc-code>

fn main() {
}

}