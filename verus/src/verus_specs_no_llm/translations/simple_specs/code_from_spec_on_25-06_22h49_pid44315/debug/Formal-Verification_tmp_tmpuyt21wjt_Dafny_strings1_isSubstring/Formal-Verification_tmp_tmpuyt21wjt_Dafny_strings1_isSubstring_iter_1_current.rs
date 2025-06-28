use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() && (exists|i: int| 0 <= i <= str.len() && isPrefixPredicate(sub, str.spec_index(i..)))
}

spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && pre <= str
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures 
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str)
{
    if pre.len() > str.len() {
        false
    } else {
        let mut i = 0;
        while i < pre.len()
            invariant 
                0 <= i <= pre.len(),
                forall|j: int| 0 <= j < i ==> pre.spec_index(j) == str.spec_index(j)
        {
            if pre.spec_index(i) != str.spec_index(i) {
                return false;
            }
            i = i + 1;
        }
        true
    }
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures
        sub.len() > str.len() ==> !res,
        res == isSubstringPredicate(sub, str)
{
    if sub.len() > str.len() {
        false
    } else {
        let mut i = 0;
        while i <= str.len() - sub.len()
            invariant 
                0 <= i <= str.len() - sub.len() + 1,
                forall|j: int| 0 <= j < i ==> !isPrefixPredicate(sub, str.spec_index(j..))
        {
            if isPrefix(sub.clone(), str.spec_index(i..)) {
                return true;
            }
            i = i + 1;
        }
        false
    }
}

}