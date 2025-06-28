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
    !isPrefixPred(pre, str)
}

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i && i + sub.len() <= str.len() && 
        sub == str.subrange(i, i + sub.len())
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    !isSubstringPred(sub, str)
}

spec fn haveCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int| 0 <= i1 && i1 + k <= str1.len() && 
        isSubstringPred(str1.subrange(i1, i1 + k), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    !haveCommonKSubstringPred(k, str1, str2)
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
    let sub_len = sub.len();
    
    if sub_len == 0 {
        // Empty sequence is always a substring
        assert(str.subrange(0, 0) == seq![]);
        assert(isSubstringPred(sub, str)) by {
            assert(sub == str.subrange(0, 0));
        }
        return true;
    }
    
    if sub_len > str_len {
        assert(!isSubstringPred(sub, str)) by {
            assert(forall|i: int| 0 <= i && i + sub_len <= str_len ==> false);
        }
        return false;
    }
    
    while i < str_len && i + sub_len <= str_len
        invariant 0 <= i <= str_len
        invariant forall|j: int| 0 <= j < i && j + sub_len <= str_len ==> 
            sub != str.subrange(j, j + sub_len)
        invariant sub_len > 0
        invariant sub_len <= str_len
    {
        if i + sub_len > str_len {
            break;
        }
        
        let current_sub = str.subrange(i as int, i as int + sub_len);
        
        if sub == current_sub {
            assert(0 <= i as int && i as int + sub_len <= str_len);
            assert(sub == str.subrange(i as int, i as int + sub_len));
            assert(isSubstringPred(sub, str));
            return true;
        }
        
        i += 1;
    }
    
    // At this point, we've checked all possible positions
    assert(!isSubstringPred(sub, str)) by {
        assert(forall|j: int| 0 <= j && j + sub_len <= str_len ==> 
               sub != str.subrange(j, j + sub_len));
    }
    false
}

fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
    ensures !found <==> haveNotCommonKSubstringPred(k, str1, str2)
{
    if k == 0 {
        // Empty substring is always a substring of any string
        assert(isSubstringPred(seq![], str2)) by {
            assert(str2.subrange(0, 0) == seq![]);
        }
        assert(haveCommonKSubstringPred(k, str1, str2)) by {
            assert(0 <= 0 && 0 + k <= str1.len());
            assert(str1.subrange(0, 0 + k) == seq![]);
            assert(isSubstringPred(str1.subrange(0, 0 + k), str2));
        }
        return true;
    }
    
    let mut i: usize = 0;
    let str1_len = str1.len();
    
    if k > str1_len {
        assert(!haveCommonKSubstringPred(k, str1, str2)) by {
            assert(forall|i1: int| 0 <= i1 && i1 + k <= str1_len ==> false);
        }
        return false;
    }
    
    while i < str1_len && i + k <= str1_len
        invariant 0 <= i <= str1_len
        invariant k > 0
        invariant forall|j: int| 0 <= j < i && j + k <= str1_len ==> 
            !isSubstringPred(str1.subrange(j, j + k), str2)
    {
        if i + k > str1_len {
            break;
        }
        
        let substring = str1.subrange(i as int, i as int + k);
        let is_substr = isSubstring(substring, str2);
        
        if is_substr {
            assert(isSubstringPred(str1.subrange(i as int, i as int + k), str2));
            assert(haveCommonKSubstringPred(k, str1, str2));
            return true;
        }
        
        assert(!isSubstringPred(str1.subrange(i as int, i as int + k), str2));
        i += 1;
    }
    
    // At this point, we've checked all possible k-length substrings
    assert(!haveCommonKSubstringPred(k, str1, str2)) by {
        assert(forall|j: int| 0 <= j && j + k <= str1_len ==> 
               !isSubstringPred(str1.subrange(j, j + k), str2));
    }
    false
}

}