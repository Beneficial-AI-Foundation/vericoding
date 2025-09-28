use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_subrange_twice<T>(s: Seq<T>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= s.len(),
    ensures
        s.subrange(i, j).subrange(0, j - i) == s.subrange(i, j),
        s.subrange(i, k).subrange(0, j - i) == s.subrange(i, j),
{
}

spec fn common_prefix_property(str1: Seq<char>, str2: Seq<char>, n: int) -> bool
    recommends n >= 0 && n <= str1.len() && n <= str2.len()
{
    forall|i: int| 0 <= i < n ==> str1[i] == str2[i]
}

proof fn lemma_common_prefix_property_implies_equality(str1: Seq<char>, str2: Seq<char>, n: int)
    requires
        n >= 0 && n <= str1.len() && n <= str2.len(),
        common_prefix_property(str1, str2, n),
    ensures
        str1.subrange(0, n) == str2.subrange(0, n),
{
}

proof fn lemma_common_prefix_property_monotonic(str1: Seq<char>, str2: Seq<char>, n: int, m: int)
    requires
        0 <= n <= m <= str1.len() && m <= str2.len(),
        common_prefix_property(str1, str2, m),
    ensures
        common_prefix_property(str1, str2, n),
{
}

spec fn find_first_mismatch(str1: Seq<char>, str2: Seq<char>, max_n: int) -> int
    recommends max_n >= 0 && max_n <= str1.len() && max_n <= str2.len()
{
    if max_n == 0 {
        0
    } else if !common_prefix_property(str1, str2, max_n) {
        find_first_mismatch(str1, str2, max_n - 1)
    } else {
        max_n
    }
}

proof fn lemma_find_first_mismatch_properties(str1: Seq<char>, str2: Seq<char>, max_n: int)
    requires
        max_n >= 0 && max_n <= str1.len() && max_n <= str2.len(),
    ensures
        find_first_mismatch(str1, str2, max_n) <= max_n,
        common_prefix_property(str1, str2, find_first_mismatch(str1, str2, max_n)),
        find_first_mismatch(str1, str2, max_n) == max_n || !common_prefix_property(str1, str2, find_first_mismatch(str1, str2, max_n) + 1),
{
    if max_n == 0 {
    } else if !common_prefix_property(str1, str2, max_n) {
        lemma_find_first_mismatch_properties(str1, str2, max_n - 1);
    } else {
    }
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
    let max_len_usize = if str1.len() < str2.len() { str1.len() } else { str2.len() };
    let mut i: usize = 0;
    
    while i < max_len_usize
        invariant
            i <= max_len_usize,
            common_prefix_property(str1, str2, i as int),
        decreases max_len_usize - i,
    {
        if str1.index(i) == str2.index(i) {
            i = i + 1;
        } else {
            break;
        }
    }
    
    proof {
        let n = i as int;
        lemma_common_prefix_property_implies_equality(str1, str2, n);
    }
    
    str1.subrange(0, i as int)
}
// </vc-code>

fn main() {
}

}