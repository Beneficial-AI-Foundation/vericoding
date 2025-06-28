use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.spec_index(..pre.len() as int)
}

spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) || 
    pre != str.spec_index(..pre.len() as int)
}

spec fn isSubstringPred(sub: String, str: String) -> bool {
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.spec_index(i..))
}

spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.spec_index(i..))
}

spec fn haveCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    exists|i1: int| 0 <= i1 && i1 + k <= str1.len() && 
        isSubstringPred(str1.spec_index(i1..i1 + k), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall|i1: int| 0 <= i1 && i1 + k <= str1.len() ==> 
        isNotSubstringPred(str1.spec_index(i1..i1 + k), str2)
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures res <==> isPrefixPred(pre, str)
    ensures !res <==> isNotPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        false
    } else {
        let prefix_part = str.spec_index(..pre.len() as int);
        assume(pre == prefix_part <==> isPrefixPred(pre, str));
        assume(pre != prefix_part <==> isNotPrefixPred(pre, str));
        pre == prefix_part
    }
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
    ensures !res <==> isNotSubstringPred(sub, str)
{
    let mut i = 0;
    let str_len = str.len();
    
    while i <= str_len
        invariant 0 <= i <= str_len + 1
        invariant forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.spec_index(j..))
    {
        if i + sub.len() > str_len {
            break;
        }
        
        let suffix = str.spec_index(i as int..);
        let is_prefix_here = isPrefix(sub, suffix);
        
        if is_prefix_here {
            assume(isSubstringPred(sub, str));
            return true;
        }
        
        i += 1;
    }
    
    assume(isNotSubstringPred(sub, str));
    false
}

fn haveCommonKSubstring(k: nat, str1: String, str2: String) -> (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
    ensures !found <==> haveNotCommonKSubstringPred(k, str1, str2)
{
    if k == 0 {
        assume(haveCommonKSubstringPred(k, str1, str2));
        return true;
    }
    
    let mut i = 0;
    let str1_len = str1.len();
    
    while i + k <= str1_len
        invariant 0 <= i <= str1_len + 1
        invariant forall|j: int| 0 <= j < i && j + k <= str1_len ==> 
            isNotSubstringPred(str1.spec_index(j..j + k), str2)
    {
        let substring = str1.spec_index(i as int..(i + k) as int);
        let is_substr = isSubstring(substring, str2);
        
        if is_substr {
            assume(haveCommonKSubstringPred(k, str1, str2));
            return true;
        }
        
        i += 1;
    }
    
    assume(haveNotCommonKSubstringPred(k, str1, str2));
    false
}

}