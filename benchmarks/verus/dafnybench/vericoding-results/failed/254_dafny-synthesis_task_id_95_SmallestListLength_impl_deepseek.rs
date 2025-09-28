use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn find_min_index_lemma(s: Seq<Seq<int>>, start: int, end: int, min_idx: int) 
    requires
        0 <= start <= end <= s.len(),
        0 <= min_idx < s.len(),
        forall|i: int| start <= i < end ==> s[min_idx].len() <= s[i].len()
    ensures
        exists|i: int| start <= i < end && s[i].len() == s[min_idx].len()
{
    if start < end {
        assert(s[min_idx].len() <= s[start].len());
        if s[min_idx].len() == s[start].len() {
            assert(0 <= start < s.len());
            assert(s[start].len() == s[min_idx].len());
        } else {
            find_min_index_lemma(s, start + 1, end, min_idx);
        }
    }
}

proof fn min_length_exists(s: Seq<Seq<int>>, min_val: nat)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> min_val <= s[i].len()
    ensures
        exists|i: int| 0 <= i < s.len() && s[i].len() == min_val
{
    let mut min_idx: usize = 0;
    let mut i: int = 1;
    
    while i < s.len() as int
        invariant
            0 <= i <= s.len() as int,
            0 <= min_idx < s.len(),
            forall|j: int| 0 <= j < i ==> s[min_idx].len() <= s[j].len()
    {
        if s[i as usize].len() < s[min_idx].len() {
            min_idx = i as usize;
        }
        i = i + 1;
    }
    
    find_min_index_lemma(s, 0, s.len() as int, min_idx as int);
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
    let mut min_len: usize = s[0].len();
    let mut i: usize = 1;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            min_len <= s[0].len(),
            forall|j: int| 0 <= j < i ==> min_len <= s[j as usize].len(),
            exists|j: int| 0 <= j < i && s[j as usize].len() == min_len
    {
        if s[i].len() < min_len {
            min_len = s[i].len();
        }
        proof {
            if min_len == s[i].len() {
                assert(0 <= i < s.len());
                assert(s[i].len() == min_len);
            } else {
                assert(min_len < s[i].len());
                assert(forall|j: int| 0 <= j < i ==> min_len <= s[j as usize].len());
            }
        }
        i = i + 1;
    }
    
    proof {
        min_length_exists(s, min_len);
    }
    
    min_len as int
}
// </vc-code>

fn main() {
}

}