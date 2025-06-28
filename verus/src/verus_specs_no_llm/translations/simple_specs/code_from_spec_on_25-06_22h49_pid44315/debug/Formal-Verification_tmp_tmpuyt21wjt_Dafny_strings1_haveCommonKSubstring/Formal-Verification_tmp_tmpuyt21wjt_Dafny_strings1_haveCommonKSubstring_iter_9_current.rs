use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPredicate(pre: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= pre.len() && 
    (forall|i: int| 0 <= i < pre.len() ==> pre[i] == str[i])
}

spec fn isSubstringPredicate(sub: Seq<char>, str: Seq<char>) -> bool {
    sub.len() <= str.len() && 
    (exists|i: int| 0 <= i <= str.len() - sub.len() && 
        isPrefixPredicate(sub, str.subrange(i, i + sub.len())))
}

spec fn haveCommonKSubstringPredicate(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    str1.len() >= k && str2.len() >= k && 
    (exists|i: int| 0 <= i <= str1.len() - k && 
        isSubstringPredicate(str1.subrange(i, i + k), str2))
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures 
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str)
{
    if pre.len() > str.len() {
        assert(!isPrefixPredicate(pre, str));
        false
    } else {
        let mut i: usize = 0;
        while i < pre.len()
            invariant 
                0 <= i <= pre.len(),
                pre.len() <= str.len(),
                forall|j: int| 0 <= j < i ==> pre[j] == str[j]
        {
            if pre[i as int] != str[i as int] {
                assert(!isPrefixPredicate(pre, str));
                return false;
            }
            i += 1;
        }
        assert(i == pre.len());
        assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]);
        assert(isPrefixPredicate(pre, str));
        true
    }
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res == isSubstringPredicate(sub, str)
{
    if sub.len() > str.len() {
        assert(!isSubstringPredicate(sub, str));
        return false;
    }
    
    let mut i: usize = 0;
    assert(str.len() >= sub.len());
    let limit = (str.len() - sub.len()) as usize;
    
    while i <= limit
        invariant 
            0 <= i <= limit + 1,
            sub.len() <= str.len(),
            limit == str.len() - sub.len(),
            i <= str.len(),
            forall|j: int| 0 <= j < i ==> !isPrefixPredicate(sub, str.subrange(j, j + sub.len()))
        decreases limit + 1 - i
    {
        assert(i as int <= str.len() - sub.len());
        assert(i as int + sub.len() <= str.len());
        let substr = str.subrange(i as int, i as int + sub.len());
        assert(substr.len() == sub.len());
        
        if isPrefix(sub, substr) {
            assert(isPrefixPredicate(sub, substr));
            assert(0 <= i <= str.len() - sub.len());
            assert(isSubstringPredicate(sub, str));
            return true;
        }
        assert(!isPrefixPredicate(sub, str.subrange(i as int, i as int + sub.len())));
        i += 1;
    }
    
    assert(i as int == str.len() - sub.len() + 1);
    assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> !isPrefixPredicate(sub, str.subrange(j, j + sub.len())));
    assert(!isSubstringPredicate(sub, str));
    false
}

fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        str1.len() < k || str2.len() < k ==> !found,
        found == haveCommonKSubstringPredicate(k, str1, str2)
{
    if str1.len() < k || str2.len() < k {
        assert(!haveCommonKSubstringPredicate(k, str1, str2));
        return false;
    }
    
    let mut i: usize = 0;
    assert(str1.len() >= k);
    let limit = (str1.len() - k as int) as usize;
    
    while i <= limit
        invariant 
            0 <= i <= limit + 1,
            str1.len() >= k,
            str2.len() >= k,
            limit == str1.len() - k,
            i <= str1.len(),
            forall|j: int| 0 <= j < i ==> !isSubstringPredicate(str1.subrange(j, j + k as int), str2)
        decreases limit + 1 - i
    {
        assert(i as int <= str1.len() - k as int);
        assert(i as int + k as int <= str1.len());
        let substring = str1.subrange(i as int, i as int + k as int);
        assert(substring.len() == k);
        
        if isSubstring(substring, str2) {
            assert(isSubstringPredicate(substring, str2));
            assert(substring == str1.subrange(i as int, i as int + k as int));
            assert(0 <= i <= str1.len() - k);
            assert(haveCommonKSubstringPredicate(k, str1, str2));
            return true;
        }
        assert(!isSubstringPredicate(str1.subrange(i as int, i as int + k as int), str2));
        i += 1;
    }
    
    assert(i as int == str1.len() - k as int + 1);
    assert(forall|j: int| 0 <= j <= str1.len() - k ==> !isSubstringPredicate(str1.subrange(j, j + k as int), str2));
    assert(!haveCommonKSubstringPredicate(k, str1, str2));
    false
}

}