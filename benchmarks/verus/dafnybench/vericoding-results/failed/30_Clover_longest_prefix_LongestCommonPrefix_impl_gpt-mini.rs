use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    let len1 = str1.len();
    let len2 = str2.len();
    let mut i: nat = 0;
    while i < len1 && i < len2
        invariant i <= len1;
        invariant i <= len2;
        invariant forall |j: int| 0 <= j && j < (i as int) ==> #[trigger] str1[@j] == str2[@j];
        decreases len1 - i;
    {
        let ii: int = i as int;
        if str1[@ii] == str2[@ii] {
            i = i + 1;
        } else {
            break;
        }
    }
    let prefix = str1.subrange(0, i as int);
    proof {
        assert(prefix.len() == i);
        assert(prefix.len() <= len1);
        assert(prefix == str1.subrange(0, prefix.len() as int));
        // use the invariant to show elements equal up to prefix.len()
        assert(forall |j: int| 0 <= j && j < (prefix.len() as int) ==> #[trigger] str1[@j] == str2[@j]);
        // show prefix equals corresponding subrange of str2
        assert(forall |j: int| 0 <= j && j < (prefix.len() as int) ==> #[trigger] prefix[@j] == str2[@j]);
        proof {
            assert(forall |j: int| 0 <= j && j < (prefix.len() as int) ==> prefix[@j] == str1[@j]);
            assert(forall |j: int| 0 <= j && j < (prefix.len() as int) ==> str1[@j] == str2[@j]);
        }
        assert(prefix == str2.subrange(0, prefix.len() as int));
        // show the third disjunctive condition
        let ii: int = i as int;
        assert(!(i < len1 && i < len2 && str1[@ii] == str2[@ii]));
        if i < len1 {
            if i < len2 {
                assert(str1[@ii] != str2[@ii]);
            } else {
                // i >= len2 and invariant i <= len2 imply i == len2
                assert(i == len2);
            }
        } else {
            // i >= len1 and invariant i <= len1 imply i == len1
            assert(i == len1);
        }
    }
    return prefix;
}
// </vc-code>

fn main() {
}

}