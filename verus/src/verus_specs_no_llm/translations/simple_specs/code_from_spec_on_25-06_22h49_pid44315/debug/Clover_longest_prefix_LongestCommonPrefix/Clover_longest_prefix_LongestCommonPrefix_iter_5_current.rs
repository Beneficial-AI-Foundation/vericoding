use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LongestCommonPrefix(str1: Seq<char>, str2: Seq<char>) -> (prefix: Seq<char>)
    ensures
        prefix.len() <= str1.len() && prefix == str1.subrange(0, prefix.len() as int),
        prefix.len() <= str2.len() && prefix == str2.subrange(0, prefix.len() as int),
        prefix.len() == str1.len() || prefix.len() == str2.len() || (prefix.len() < str1.len() && prefix.len() < str2.len() && str1[prefix.len() as int] != str2[prefix.len() as int])
{
    let mut i: usize = 0;
    let min_len = if str1.len() < str2.len() { str1.len() } else { str2.len() };
    
    while i < min_len
        invariant
            i <= min_len,
            min_len == if str1.len() < str2.len() { str1.len() } else { str2.len() },
            min_len <= str1.len(),
            min_len <= str2.len(),
            forall|j: int| 0 <= j < i ==> str1[j] == str2[j],
            i <= str1.len(),
            i <= str2.len(),
    {
        if str1[i as int] != str2[i as int] {
            break;
        }
        i = i + 1;
    }
    
    let result = str1.subrange(0, i as int);
    
    // Prove first postcondition
    assert(result.len() == i);
    assert(result == str1.subrange(0, result.len() as int));
    
    // Prove second postcondition - result is also a prefix of str2
    assert(result == str2.subrange(0, result.len() as int)) by {
        let str2_prefix = str2.subrange(0, result.len() as int);
        assert(result.len() == str2_prefix.len());
        assert(forall|j: int| 0 <= j < result.len() ==> {
            result[j] == str1[j] && str1[j] == str2[j] && str2[j] == str2_prefix[j]
        });
    };
    
    // Prove third postcondition
    if result.len() < str1.len() && result.len() < str2.len() {
        assert(i < min_len || (i == min_len && min_len < str1.len() && min_len < str2.len()));
        if i < min_len {
            // Loop terminated due to character mismatch
            assert(str1[i as int] != str2[i as int]);
            assert(result.len() == i);
        } else {
            // Loop terminated because we reached min_len
            assert(i == min_len);
            if min_len == str1.len() {
                assert(result.len() == str1.len());
                assert(false); // This contradicts our assumption
            } else {
                assert(min_len == str2.len());
                assert(result.len() == str2.len());
                assert(false); // This contradicts our assumption
            }
        }
    }
    
    result
}

}