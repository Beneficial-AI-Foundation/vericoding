// ATOM 
spec fn isPrefixPred(pre: &str, str: &str) -> bool
{
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

// ATOM 
spec fn isNotPrefixPred(pre: &str, str: &str) -> bool
{
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

// ATOM 
proof fn PrefixNegationLemma(pre: &str, str: &str)
    ensures isPrefixPred(pre, str) <==> !isNotPrefixPred(pre, str)
    ensures !isPrefixPred(pre, str) <==> isNotPrefixPred(pre, str)
{
}

// SPEC 
pub fn isPrefix(pre: &str, str: &str) -> (res: bool)
    ensures(!res <==> isNotPrefixPred(pre, str))
    ensures(res <==> isPrefixPred(pre, str))
{
}

// ATOM 
spec fn isSubstringPred(sub: &str, str: &str) -> bool
{
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int))
}

// ATOM 
spec fn isNotSubstringPred(sub: &str, str: &str) -> bool
{
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))
}

// ATOM 
proof fn SubstringNegationLemma(sub: &str, str: &str)
    ensures isSubstringPred(sub, str) <==> !isNotSubstringPred(sub, str)
    ensures !isSubstringPred(sub, str) <==> isNotSubstringPred(sub, str)
{
}

// SPEC 
pub fn isSubstring(sub: &str, str: &str) -> (res: bool)
    ensures(res <==> isSubstringPred(sub, str))
    ensures(res ==> isSubstringPred(sub, str))
    ensures(isSubstringPred(sub, str) ==> res)
    ensures(isSubstringPred(sub, str) ==> res)
    ensures(!res <==> isNotSubstringPred(sub, str))
{
}

// ATOM 
spec fn haveCommonKSubstringPred(k: nat, str1: &str, str2: &str) -> bool
{
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && isSubstringPred(str1.subrange(i1, j1), str2)
}

// ATOM 
spec fn haveNotCommonKSubstringPred(k: nat, str1: &str, str2: &str) -> bool
{
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> isNotSubstringPred(str1.subrange(i1, j1), str2)
}

// ATOM 
proof fn commonKSubstringLemma(k: nat, str1: &str, str2: &str)
    ensures haveCommonKSubstringPred(k, str1, str2) <==> !haveNotCommonKSubstringPred(k, str1, str2)
    ensures !haveCommonKSubstringPred(k, str1, str2) <==> haveNotCommonKSubstringPred(k, str1, str2)
{
}

// SPEC 
pub fn haveCommonKSubstring(k: nat, str1: &str, str2: &str) -> (found: bool)
    ensures(found <==> haveCommonKSubstringPred(k, str1, str2))
    ensures(!found <==> haveNotCommonKSubstringPred(k, str1, str2))
{
}

// SPEC 
pub fn maxCommonSubstringLength(str1: &str, str2: &str) -> (len: nat)
    requires(str1.len() <= str2.len())
    ensures(forall|k: int| len < k <= str1.len() ==> !haveCommonKSubstringPred(k as nat, str1, str2))
    ensures(haveCommonKSubstringPred(len, str1, str2))
{
}