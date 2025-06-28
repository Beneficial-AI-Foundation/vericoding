use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int))
}

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures !res <==> isNotPrefixPred(pre, str)
    ensures res <==> isPrefixPred(pre, str)
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
    
    while i <= str.len()
        invariant 
            0 <= i <= str.len() + 1,
            forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int))
    {
        if i <= str.len() && isPrefix(sub, str.subrange(i as int, str.len() as int)) {
            // Prove that we found a valid substring position
            assert(isPrefixPred(sub, str.subrange(i as int, str.len() as int)));
            assert(0 <= i <= str.len());
            assert(isSubstringPred(sub, str));
            return true;
        }
        
        // Ensure we don't overflow and maintain loop termination
        if i >= str.len() {
            break;
        }
        i = i + 1;
    }
    
    // Prove that no valid substring position exists
    assert(forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
    assert(i > str.len());
    
    // Strengthen the assertion to cover all valid positions
    assert(forall|j: int| 0 <= j <= str.len() ==> {
        if j < i {
            isNotPrefixPred(sub, str.subrange(j, str.len() as int))
        } else {
            // j >= i > str.len(), so this case is impossible
            true
        }
    });
    
    assert(forall|j: int| 0 <= j <= str.len() ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
    assert(isNotSubstringPred(sub, str));
    false
}

}