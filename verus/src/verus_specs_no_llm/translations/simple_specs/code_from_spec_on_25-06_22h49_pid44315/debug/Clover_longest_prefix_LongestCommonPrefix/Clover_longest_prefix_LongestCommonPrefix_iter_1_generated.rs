use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LongestCommonPrefix(str1: Seq<char>, str2: Seq<char>) -> (prefix: Seq<char>)
    ensures
        prefix.len() <= str1.len() && prefix == str1.spec_index(0..prefix.len()),
        prefix.len() <= str2.len() && prefix == str2.spec_index(0..prefix.len()),
        prefix.len() == str1.len() || prefix.len() == str2.len() || (prefix.len() < str1.len() && prefix.len() < str2.len() && str1.spec_index(prefix.len()) != str2.spec_index(prefix.len()))
{
    let mut i: usize = 0;
    let min_len = if str1.len() < str2.len() { str1.len() } else { str2.len() };
    
    while i < min_len
        invariant
            i <= min_len,
            min_len <= str1.len(),
            min_len <= str2.len(),
            forall|j: int| 0 <= j < i ==> str1.spec_index(j) == str2.spec_index(j)
    {
        if str1.spec_index(i) != str2.spec_index(i) {
            break;
        }
        i = i + 1;
    }
    
    str1.spec_index(0..i)
}

}