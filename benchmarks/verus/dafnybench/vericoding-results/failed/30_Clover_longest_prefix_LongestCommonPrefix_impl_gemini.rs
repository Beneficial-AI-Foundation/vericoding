// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implemented an iterative proof function to find the length */
proof fn get_prefix_len(str1: Seq<char>, str2: Seq<char>) -> (len: int)
    ensures
        0 <= len <= str1.len(),
        0 <= len <= str2.len(),
        str1.subrange(0, len) == str2.subrange(0, len),
        len == str1.len() || len == str2.len() || str1[len] != str2[len],
{
    let mut i: int = 0;
    while i < str1.len() && i < str2.len() && str1[i] == str2[i]
        invariant
            0 <= i <= str1.len(),
            0 <= i <= str2.len(),
            str1.subrange(0, i) == str2.subrange(0, i),
        decreases str1.len() - i
    {
        i = i + 1;
    }
    i
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
    /* code modified by LLM (iteration 5): called new helper and used its result, removing the cast */
    let len = get_prefix_len(str1, str2);
    str1.subrange(0, len)
}
// </vc-code>

}
fn main() {}