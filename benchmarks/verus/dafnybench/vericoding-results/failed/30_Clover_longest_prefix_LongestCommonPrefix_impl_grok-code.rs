use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed
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
    let ghost mut pos: nat = 0;
    while pos < str1.len() && pos < str2.len() && str1[pos] == str2[pos]
        invariant
            pos <= str1.len() && pos <= str2.len(),
            forall |j: int| 0 <= j < pos ==> str1[j] == str2[j]
        decreases str1.len() as int - pos as int
    {
        pos = pos + 1;
    }
    str1.subrange(0, pos as int)
}
// </vc-code>

fn main() {
}

}