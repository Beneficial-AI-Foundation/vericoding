// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn LongestCommonPrefix(str1: Seq<char>, str2: Seq<char>) -> (prefix: Seq<char>)
    ensures prefix.len() <= str1.len() and prefix == str1[0..prefix.len()]and prefix.len() <= str2.len() and prefix == str2[0..prefix.len()],
            prefix.len()==str1.len() | .len()prefix==.len()str2 .len() (str1[.len()prefix]!=str2[.len()prefix|])
{
}

}