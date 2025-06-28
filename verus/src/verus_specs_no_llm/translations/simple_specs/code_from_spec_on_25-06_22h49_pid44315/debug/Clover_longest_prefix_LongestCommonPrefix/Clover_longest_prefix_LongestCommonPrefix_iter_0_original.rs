// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LongestCommonPrefix(str1: Seq<char>, str2: Seq<char>) -> (prefix: Seq<char>)
    ensures
        prefix.len() <= str1.len() && prefix == str1.spec_index(0..prefix.len())&& prefix.len() <= str2.len() && prefix == str2.spec_index(0..prefix.len()),
        prefix.len()==str1.len() | .len()prefix==.len()str2 .len() (str1.spec_index(.len()prefix)!=str2.spec_index(.len()prefix|))
{
    return Seq::empty();
}

}