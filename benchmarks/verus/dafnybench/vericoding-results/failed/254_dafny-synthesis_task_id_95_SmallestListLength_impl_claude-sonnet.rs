use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut i: usize = 1;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> min_len <= s[j].len(),
            exists|j: int| 0 <= j < i && min_len == #[trigger] s[j].len(),
    {
        if s[i as int].len() < min_len {
            min_len = s[i as int].len();
        }
        i = i + 1;
    }
    
    proof {
        assert(forall|j: int| 0 <= j < s.len() ==> min_len <= s[j].len());
        assert(exists|j: int| 0 <= j < s.len() && min_len == #[trigger] s[j].len());
    }
    
    min_len
}
// </vc-code>

fn main() {
}

}