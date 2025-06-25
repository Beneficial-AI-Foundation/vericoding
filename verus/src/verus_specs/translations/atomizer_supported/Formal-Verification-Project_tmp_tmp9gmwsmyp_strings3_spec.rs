// ATOM 
pub open spec fn isPrefixPred(pre: String, str: String) -> bool
{
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

// ATOM 
pub open spec fn isNotPrefixPred(pre: String, str: String) -> bool
{
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

// ATOM 
pub proof fn PrefixNegationLemma(pre: String, str: String)
    ensures isPrefixPred(pre, str) <==> !isNotPrefixPred(pre, str)
    ensures !isPrefixPred(pre, str) <==> isNotPrefixPred(pre, str)
{
}

// SPEC 
pub fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures !res <==> isNotPrefixPred(pre, str)
    ensures res <==> isPrefixPred(pre, str)
{
}

// ATOM 
pub open spec fn isSubstringPred(sub: String, str: String) -> bool
{
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len()))
}

// ATOM 
pub open spec fn isNotSubstringPred(sub: String, str: String) -> bool
{
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len()))
}

// ATOM 
pub proof fn SubstringNegationLemma(sub: String, str: String)
    ensures isSubstringPred(sub, str) <==> !isNotSubstringPred(sub, str)
    ensures !isSubstringPred(sub, str) <==> isNotSubstringPred(sub, str)
{
}

// SPEC 
pub fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
}

// ATOM 
pub open spec fn haveCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool
{
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && isSubstringPred(str1.subrange(i1, j1), str2)
}

// ATOM 
pub open spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool
{
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> isNotSubstringPred(str1.subrange(i1, j1), str2)
}

// ATOM 
pub proof fn commonKSubstringLemma(k: nat, str1: String, str2: String)
    ensures haveCommonKSubstringPred(k, str1, str2) <==> !haveNotCommonKSubstringPred(k, str1, str2)
    ensures !haveCommonKSubstringPred(k, str1, str2) <==> haveNotCommonKSubstringPred(k, str1, str2)
{
}

// SPEC 
pub fn haveCommonKSubstring(k: nat, str1: String, str2: String) -> (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
}

// ATOM 
pub proof fn haveCommon0SubstringLemma(str1: String, str2: String)
    ensures haveCommonKSubstringPred(0, str1, str2)
{
}

// SPEC 
pub fn maxCommonSubstringLength(str1: String, str2: String) -> (len: nat)
    requires str1.len() <= str2.len()
    ensures forall|k: int| len < k <= str1.len() ==> !haveCommonKSubstringPred(k, str1, str2)
    ensures haveCommonKSubstringPred(len, str1, str2)
{
}