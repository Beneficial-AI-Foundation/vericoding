use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && 
    (forall|j: int| 0 <= j < pre.len() ==> pre.spec_index(j) == str.spec_index(j))
}

spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() && 
    (exists|i: int| 0 <= i <= str.len() - sub.len() && isPrefixPredicate(sub, str.spec_index(i..)))
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
                assert(forall|j: int| 0 <= j < pre.len() ==> pre.spec_index(j) == str.spec_index(j) is false);
                return false;
            }
            i = i + 1;
        }
        assert(forall|j: int| 0 <= j < pre.len() ==> pre.spec_index(j) == str.spec_index(j));
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
    } else if sub.len() == 0 {
        assert(isPrefixPredicate(sub, str.spec_index(0..)));
        true
    } else {
        let mut i = 0;
        while i <= str.len() - sub.len()
            invariant 
                0 <= i <= str.len() - sub.len() + 1,
                sub.len() > 0,
                forall|j: int| 0 <= j < i ==> !isPrefixPredicate(sub, str.spec_index(j..))
        {
            let substr = str.spec_index(i..);
            if isPrefix(sub.clone(), substr) {
                assert(isPrefixPredicate(sub, str.spec_index(i..)));
                assert(0 <= i <= str.len() - sub.len());
                return true;
            }
            assert(!isPrefixPredicate(sub, str.spec_index(i..)));
            i = i + 1;
        }
        assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> !isPrefixPredicate(sub, str.spec_index(j..)));
        false
    }
}

}