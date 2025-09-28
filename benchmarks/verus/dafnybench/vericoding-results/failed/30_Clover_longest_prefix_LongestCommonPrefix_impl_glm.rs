use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n = str1.len().min(str2.len());
    let mut i: nat = 0;
    while i < n && str1@[i] == str2@[i]
        invariant 
            i <= n,
            str1.subrange(0, i as int) == str2.subrange(0, i as int)
    {
        i = i + 1;
    }
    str1.subrange(0, i as int)
}
// </vc-code>

fn main() {
}

}