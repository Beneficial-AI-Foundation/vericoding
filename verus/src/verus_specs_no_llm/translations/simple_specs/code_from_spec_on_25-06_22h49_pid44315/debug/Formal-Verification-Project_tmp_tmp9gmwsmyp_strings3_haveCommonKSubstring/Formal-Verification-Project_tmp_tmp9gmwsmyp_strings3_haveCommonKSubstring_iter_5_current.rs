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

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i && i + sub.len() <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int))
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i && i + sub.len() <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))
}

spec fn haveCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int| 0 <= i1 && i1 + k <= str1.len() && 
        isSubstringPred(str1.subrange(i1, i1 + k), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int| 0 <= i1 && i1 + k <= str1.len() ==> 
        isNotSubstringPred(str1.subrange(i1, i1 + k), str2)
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> isPrefixPred(pre, str)
    ensures !res <==> isNotPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        false
    } else {
        let prefix_part = str.subrange(0, pre.len() as int);
        pre == prefix_part
    }
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
    ensures !res <==> isNotSubstringPred(sub, str)
{
    let mut i: usize = 0;
    let str_len = str.len();
    
    while i + sub.len() <= str_len
        invariant 0 <= i <= str_len
        invariant forall|j: int| 0 <= j < i && j + sub.len() <= str_len ==> 
            isNotPrefixPred(sub, str.subrange(j, str_len as int))
        invariant forall|j: int| 0 <= j < i && j + sub.len() <= str_len ==> 
            !isPrefixPred(sub, str.subrange(j, str_len as int))
    {
        let suffix = str.subrange(i as int, str_len as int);
        let is_prefix_here = isPrefix(sub, suffix);
        
        if is_prefix_here {
            assert(isPrefixPred(sub, str.subrange(i as int, str_len as int)));
            return true;
        }
        
        assert(isNotPrefixPred(sub, str.subrange(i as int, str_len as int)));
        i += 1;
    }
    
    // At this point, we've checked all possible positions
    assert(forall|j: int| 0 <= j && j + sub.len() <= str_len ==> 
           isNotPrefixPred(sub, str.subrange(j, str_len as int)));
    false
}

fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
    ensures !found <==> haveNotCommonKSubstringPred(k, str1, str2)
{
    if k == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    let str1_len = str1.len();
    
    while i + k <= str1_len
        invariant 0 <= i <= str1_len
        invariant forall|j: int| 0 <= j < i && j + k <= str1_len ==> 
            isNotSubstringPred(str1.subrange(j, j + k), str2)
        invariant forall|j: int| 0 <= j < i && j + k <= str1_len ==> 
            !isSubstringPred(str1.subrange(j, j + k), str2)
    {
        let substring = str1.subrange(i as int, (i + k) as int);
        let is_substr = isSubstring(substring, str2);
        
        if is_substr {
            assert(isSubstringPred(str1.subrange(i as int, (i + k) as int), str2));
            return true;
        }
        
        assert(isNotSubstringPred(str1.subrange(i as int, (i + k) as int), str2));
        i += 1;
    }
    
    // At this point, we've checked all possible k-length substrings
    assert(forall|j: int| 0 <= j && j + k <= str1_len ==> 
           isNotSubstringPred(str1.subrange(j, j + k), str2));
    false
}

}