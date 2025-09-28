use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn sequences_equal_up_to(s1: Seq<char>, s2: Seq<char>, len: int) -> bool {
    forall|j: int| 0 <= j < len ==> s1[j] == s2[j]
}
// </vc-helpers>

// <vc-spec>
fn longest_common_prefix(str1: Seq<char>, str2: Seq<char>) -> (prefix: Seq<char>)
    ensures 
        prefix.len() <= str1.len() && prefix == str1.subrange(0, prefix.len() as int) &&
        prefix.len() <= str2.len() && prefix == str2.subrange(0, prefix.len() as int),
        prefix.len() == str1.len() || prefix.len() == str2.len() || 
        (str1[prefix.len() as int] != str2[prefix.len() as int])
// </vc-spec>
// <vc-code>
{
    let min_len = if str1.len() <= str2.len() { str1.len() } else { str2.len() };
    let mut i: usize = 0;
    
    while i < min_len
        invariant
            i <= min_len,
            min_len <= str1.len(),
            min_len <= str2.len(),
            sequences_equal_up_to(str1, str2, i as int),
    {
        if str1[i] != str2[i] {
            break;
        }
        i = i + 1;
    }
    
    let prefix = str1.subrange(0, i as int);
    
    assert(prefix.len() == i);
    assert(prefix.len() <= str1.len());
    assert(prefix.len() <= str2.len());
    assert(prefix == str1.subrange(0, prefix.len() as int));
    
    proof {
        assert(sequences_equal_up_to(str1, str2, i as int));
        assert(forall|j: int| 0 <= j < prefix.len() ==> #[trigger] prefix[j] == str1[j]);
        assert(forall|j: int| 0 <= j < prefix.len() ==> #[trigger] prefix[j] == str2[j]) by {
            assert(forall|j: int| 0 <= j < i ==> str1[j] == str2[j]);
        };
    }
    assert(prefix == str2.subrange(0, prefix.len() as int));
    
    if prefix.len() < str1.len() && prefix.len() < str2.len() {
        assert(str1[prefix.len() as int] != str2[prefix.len() as int]);
    }
    
    prefix
}
// </vc-code>

fn main() {
}

}