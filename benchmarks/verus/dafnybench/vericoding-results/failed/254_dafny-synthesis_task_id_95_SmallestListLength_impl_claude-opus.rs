use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to establish that the minimum found so far is valid
proof fn min_property_holds(s: Seq<Seq<int>>, min_len: int, up_to: int)
    requires
        0 <= up_to <= s.len(),
        up_to > 0,
        forall|j: int| 0 <= j < up_to ==> min_len <= s[j].len(),
        exists|j: int| 0 <= j < up_to && min_len == s[j].len(),
    ensures
        forall|j: int| 0 <= j < up_to ==> min_len <= s[j].len(),
        exists|j: int| 0 <= j < up_to && min_len == s[j].len(),
{
    // This proof is trivial as it just restates the requirements
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
    let mut min_len: int = s@[0].len() as int;
    let mut i: usize = 1;
    
    while i < s.len() as usize
        invariant
            1 <= i <= s.len() as usize,
            forall|j: int| 0 <= j < i as int ==> min_len <= s@[j].len(),
            exists|j: int| 0 <= j < i as int && min_len == #[trigger] s@[j].len(),
    {
        let current_len: int = s@[i as int].len() as int;
        if current_len < min_len {
            min_len = current_len;
        }
        i = i + 1;
    }
    
    assert(i == s.len() as usize);
    min_len
}
// </vc-code>

fn main() {
}

}