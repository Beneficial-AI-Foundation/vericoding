// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_LongestCommonPrefix(str1: Seq<char>, str2: Seq<char>) -> prefix: seq<char>
    ensures
        prefix.len() <= str1.len() && prefix == str1.index(0..prefix.len())&& prefix.len() <= str2.len() && prefix == str2.index(0..prefix.len()),
        prefix.len()==str1.len() | .len()prefix==.len()str2 .len() (str1.index(.len()prefix)!=str2.index(.len()prefix|))
;

proof fn lemma_LongestCommonPrefix(str1: Seq<char>, str2: Seq<char>) -> (prefix: Seq<char>)
    ensures
        prefix.len() <= str1.len() && prefix == str1.index(0..prefix.len())&& prefix.len() <= str2.len() && prefix == str2.index(0..prefix.len()),
        prefix.len()==str1.len() | .len()prefix==.len()str2 .len() (str1.index(.len()prefix)!=str2.index(.len()prefix|))
{
    Seq::empty()
}

}