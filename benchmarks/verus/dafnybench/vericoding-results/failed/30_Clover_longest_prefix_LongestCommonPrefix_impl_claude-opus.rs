use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut i: usize = 0;
    let min_len = if str1.len() < str2.len() { str1.len() } else { str2.len() };
    
    while i < min_len
        invariant
            i <= min_len,
            i <= str1.len(),
            i <= str2.len(),
            forall|j: int| 0 <= j < i as int ==> #[trigger] str1[j] == str2[j],
    {
        if str1.index(i) != str2.index(i) {
            break;
        }
        i = i + 1;
    }
    
    proof {
        assert(i <= str1.len());
        assert(i <= str2.len());
        assert(forall|j: int| 0 <= j < i as int ==> str1[j] == str2[j]);
        
        if i < str1.len() && i < str2.len() {
            assert(str1[i as int] != str2[i as int]);
        }
        
        assert(str1.subrange(0, i as int).len() == i);
        assert(str2.subrange(0, i as int).len() == i);
        assert(forall|j: int| 0 <= j < i as int ==> str1.subrange(0, i as int)[j] == str1[j]);
        assert(forall|j: int| 0 <= j < i as int ==> str2.subrange(0, i as int)[j] == str2[j]);
        assert(str1.subrange(0, i as int) == str2.subrange(0, i as int));
    }
    
    str1.subrange(0, i)
}
// </vc-code>

fn main() {
}

}