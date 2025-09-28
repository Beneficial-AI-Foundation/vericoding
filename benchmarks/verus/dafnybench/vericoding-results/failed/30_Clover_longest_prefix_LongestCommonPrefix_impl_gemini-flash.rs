use vstd::prelude::*;

verus! {

// <vc-helpers>
fn get_longer_len(a: Seq<char>, b: Seq<char>) -> (result: nat)
    ensures
        result == if a.len() >= b.len() { a.len() } else { b.len() }
{
    if a.len() >= b.len() {
        a.len()
    } else {
        b.len()
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
    let mut i: nat = 0;
    while i < str1.len() && i < str2.len()
        invariant 
            0 <= i,
            i <= str1.len(),
            i <= str2.len(),
            str1.subrange(0, i as int) == str2.subrange(0, i as int),
            str1.subrange(0, i as int).len() == i,
            str2.subrange(0, i as int).len() == i,
    {
        if str1.index(i as int) == str2.index(i as int) {
            i = (i + 1) as nat;
        } else {
            break;
        }
    }
    let prefix = str1.subrange(0, i as int);
    proof {
        assert(prefix.len() == i);
    }
    prefix
}
// </vc-code>

fn main() {
}

}