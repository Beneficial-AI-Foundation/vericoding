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
            if pre[i] != str[i] {
                assert(!(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]));
                assert(!isPrefixPredicate(pre, str));
                return false;
            }
            i = i + 1;
        }
        assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]);
        assert(str.len() >= pre.len());
        assert(isPrefixPredicate(pre, str));
        true
    }
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        sub.len() > str.len() ==> !res,
        res == isSubstringPredicate(sub, str)
{
    if sub.len() > str.len() {
        assert(!isSubstringPredicate(sub, str));
        false
    } else if sub.len() == 0 {
        assert(str.len() >= 0);
        assert(isPrefixPredicate(sub, str.subrange(0, str.len() as int))) by {
            assert(str.subrange(0, str.len() as int).len() >= sub.len());
            assert(forall|j: int| 0 <= j < sub.len() ==> sub[j] == str.subrange(0, str.len() as int)[j]);
        };
        assert(isSubstringPredicate(sub, str)) by {
            assert(0 <= 0 <= str.len() - sub.len());
        };
        true
    } else {
        let mut i: usize = 0;
        // Safe subtraction since we know sub.len() <= str.len()
        let bound = (str.len() - sub.len()) as usize;
        while i <= bound
            invariant 
                0 <= i <= bound + 1,
                bound == str.len() - sub.len(),
                sub.len() > 0,
                sub.len() <= str.len(),
                forall|j: int| 0 <= j < i ==> !isPrefixPredicate(sub, str.subrange(j, str.len() as int))
        {
            let substr = str.subrange(i as int, str.len() as int);
            
            assert(substr.len() == str.len() - i);
            assert(i <= bound);
            assert(bound == str.len() - sub.len());
            assert(substr.len() >= sub.len()) by {
                assert(str.len() - (i as int) >= sub.len());
                assert(i <= bound);
                assert(bound == str.len() - sub.len());
            };
            
            if isPrefix(sub, substr) {
                assert(isPrefixPredicate(sub, str.subrange(i as int, str.len() as int)));
                assert(0 <= i <= str.len() - sub.len());
                assert(isSubstringPredicate(sub, str)) by {
                    assert(exists|k: int| 0 <= k <= str.len() - sub.len() && isPrefixPredicate(sub, str.subrange(k, str.len() as int))) by {
                        assert(0 <= (i as int) <= str.len() - sub.len());
                        assert(isPrefixPredicate(sub, str.subrange(i as int, str.len() as int)));
                    };
                };
                return true;
            }
            assert(!isPrefixPredicate(sub, str.subrange(i as int, str.len() as int)));
            i = i + 1;
        }
        
        assert(i == bound + 1);
        assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> !isPrefixPredicate(sub, str.subrange(j, str.len() as int))) by {
            assert(forall|j: int| 0 <= j < bound + 1 ==> !isPrefixPredicate(sub, str.subrange(j, str.len() as int)));
            assert(bound == str.len() - sub.len());
        };
        
        assert(!isSubstringPredicate(sub, str)) by {
            assert(!(exists|k: int| 0 <= k <= str.len() - sub.len() && isPrefixPredicate(sub, str.subrange(k, str.len() as int))));
        };
        false
    }
}

}