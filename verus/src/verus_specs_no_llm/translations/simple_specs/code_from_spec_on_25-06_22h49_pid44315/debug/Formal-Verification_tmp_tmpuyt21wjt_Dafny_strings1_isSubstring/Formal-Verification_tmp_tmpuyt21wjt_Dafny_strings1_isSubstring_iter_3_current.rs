use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPredicate(pre: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= pre.len() && 
    (forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j])
}

spec fn isSubstringPredicate(sub: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= sub.len() && 
    (exists|i: int| 0 <= i <= str.len() - sub.len() && isPrefixPredicate(sub, str.subrange(i, str.len() as int)))
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
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
                forall|j: int| 0 <= j < i ==> pre[j] == str[j]
        {
            if pre[i] != str[i] {
                assert(!(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]));
                return false;
            }
            i = i + 1;
        }
        assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]);
        true
    }
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        sub.len() > str.len() ==> !res,
        res == isSubstringPredicate(sub, str)
{
    if sub.len() > str.len() {
        false
    } else if sub.len() == 0 {
        assert(isPrefixPredicate(sub, str.subrange(0, str.len() as int)));
        true
    } else {
        let mut i = 0;
        while i <= str.len() - sub.len()
            invariant 
                0 <= i <= str.len() - sub.len() + 1,
                sub.len() > 0,
                forall|j: int| 0 <= j < i ==> !isPrefixPredicate(sub, str.subrange(j, str.len() as int))
        {
            let substr = str.subrange(i as int, str.len() as int);
            if isPrefix(sub, substr) {
                assert(isPrefixPredicate(sub, str.subrange(i as int, str.len() as int)));
                assert(0 <= i <= str.len() - sub.len());
                return true;
            }
            assert(!isPrefixPredicate(sub, str.subrange(i as int, str.len() as int)));
            i = i + 1;
        }
        assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> !isPrefixPredicate(sub, str.subrange(j, str.len() as int)));
        false
    }
}

}