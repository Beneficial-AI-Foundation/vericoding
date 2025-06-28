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
    
    // Prove that result is a prefix of str1
    assert(result.len() <= str1.len());
    assert(result == str1.subrange(0, result.len() as int));
    
    // Prove that result is a prefix of str2
    assert(result.len() <= str2.len()) by {
        assert(i <= min_len);
        assert(min_len <= str2.len());
    }
    
    assert(result == str2.subrange(0, result.len() as int)) by {
        let str2_prefix = str2.subrange(0, result.len() as int);
        assert(result.len() == str2_prefix.len());
        
        // Prove element-wise equality
        assert(forall|j: int| 0 <= j < result.len() ==> {
            result[j] == str1[j] && str1[j] == str2[j] && str2[j] == str2_prefix[j]
        }) by {
            assert(forall|j: int| 0 <= j < i ==> str1[j] == str2[j]);
            assert(result.len() == i);
        }
        
        // Use sequence extensionality
        assert(result =~= str2_prefix);
    }
    
    // Prove the third postcondition
    if i == min_len {
        // Loop completed without breaking - all characters matched up to min_len
        if str1.len() < str2.len() {
            assert(min_len == str1.len());
            assert(result.len() == str1.len());
        } else {
            assert(min_len == str2.len());
            assert(result.len() == str2.len());
        }
    } else {
        // Loop broke early due to character mismatch
        assert(i < min_len);
        assert(i < str1.len() && i < str2.len()) by {
            assert(min_len <= str1.len() && min_len <= str2.len());
        }
        assert(str1[i as int] != str2[i as int]);
        assert(result.len() == i);
        assert(result.len() < str1.len() && result.len() < str2.len());
        assert(str1[result.len() as int] != str2[result.len() as int]);
    }
    
    result
}

}