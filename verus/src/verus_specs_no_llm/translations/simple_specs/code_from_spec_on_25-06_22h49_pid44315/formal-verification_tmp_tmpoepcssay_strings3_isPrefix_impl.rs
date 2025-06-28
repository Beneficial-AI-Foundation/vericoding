use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        assert(isNotPrefixPred(pre, str));
        return false;
    }
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> pre[j] == str[j],
        decreases pre.len() - i
    {
        if pre[i as int] != str[i as int] {
            // Prove that the strings are not equal
            assert(pre != str.subrange(0, pre.len() as int)) by {
                let substr = str.subrange(0, pre.len() as int);
                // We have a character mismatch at position i
                assert(pre[i as int] != str[i as int]);
                // Since i < pre.len() and substr.len() == pre.len(), we have i < substr.len()
                assert(i < substr.len());
                // The substring at position i should equal str at position i (by definition of subrange)
                assert(substr[i as int] == str[i as int]);
                // Therefore pre and substr differ at position i
                assert(pre[i as int] != substr[i as int]);
                // So the sequences cannot be equal
                assert(pre != substr);
            };
            
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        
        i = i + 1;
    }
    
    // After the loop, all characters match
    assert(i == pre.len());
    assert(pre.len() <= str.len());
    assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]);
    
    // Prove string equality
    assert(pre == str.subrange(0, pre.len() as int)) by {
        let substr = str.subrange(0, pre.len() as int);
        assert(pre.len() == substr.len()) by {
            // subrange(0, n) has length n when n <= original length
            assert(pre.len() <= str.len());
        };
        assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == substr[j]) by {
            assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]);
            // By definition of subrange, substr[j] == str[j] for j in range
            assert(forall|j: int| 0 <= j < substr.len() ==> substr[j] == str[j]);
        };
        // Sequences are equal if they have same length and same elements
        assert(pre.ext_equal(substr));
    };
    
    assert(isPrefixPred(pre, str));
    return true;
}

}