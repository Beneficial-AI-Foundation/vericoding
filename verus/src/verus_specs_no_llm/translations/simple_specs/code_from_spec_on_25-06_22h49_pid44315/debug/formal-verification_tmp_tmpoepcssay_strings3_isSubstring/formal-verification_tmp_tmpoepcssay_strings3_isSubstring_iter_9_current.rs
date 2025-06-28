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

proof fn lemma_prefix_equivalence(pre: Seq<char>, str: Seq<char>, res: bool)
    requires res == (pre.len() <= str.len() && (forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]))
    ensures res <==> isPrefixPred(pre, str)
{
    if res {
        assert(pre.len() <= str.len());
        assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]);
        // Prove sequence equality by extensionality
        assert(pre.len() == str.subrange(0, pre.len() as int).len());
        assert(forall|k: int| 0 <= k < pre.len() ==> pre[k] == str.subrange(0, pre.len() as int)[k]) by {
            assert(forall|k: int| 0 <= k < pre.len() ==> str.subrange(0, pre.len() as int)[k] == str[k]);
        };
        assert(pre == str.subrange(0, pre.len() as int));
    } else {
        if pre.len() <= str.len() {
            assert(exists|j: int| 0 <= j < pre.len() && pre[j] != str[j]);
            assert(pre != str.subrange(0, pre.len() as int)) by {
                let j = choose|j: int| 0 <= j < pre.len() && pre[j] != str[j];
                assert(pre[j] != str.subrange(0, pre.len() as int)[j]);
            };
        }
    }
}

proof fn lemma_not_prefix_equivalence(pre: Seq<char>, str: Seq<char>, res: bool)
    requires res == (pre.len() <= str.len() && (forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]))
    ensures !res <==> isNotPrefixPred(pre, str)
{
    lemma_prefix_equivalence(pre, str, res);
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures 
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        proof {
            assert(isNotPrefixPred(pre, str));
        }
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
                proof {
                    assert(exists|j: int| 0 <= j < pre.len() && pre[j] != str[j]);
                    assert(pre != str.subrange(0, pre.len() as int));
                    assert(isNotPrefixPred(pre, str));
                }
                return false;
            }
            i += 1;
        }
        proof {
            assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]);
            lemma_prefix_equivalence(pre, str, true);
            lemma_not_prefix_equivalence(pre, str, true);
        }
        true
    }
}

proof fn lemma_substring_found(sub: Seq<char>, str: Seq<char>, i: int)
    requires 
        0 <= i <= str.len(),
        isPrefixPred(sub, str.subrange(i, str.len() as int))
    ensures isSubstringPred(sub, str)
{
    assert(isPrefixPred(sub, str.subrange(i, str.len() as int)));
}

proof fn lemma_no_substring(sub: Seq<char>, str: Seq<char>, bound: int)
    requires 
        bound == str.len() - sub.len() + 1,
        sub.len() <= str.len(),
        forall|j: int| 0 <= j < bound ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int))
    ensures isNotSubstringPred(sub, str)
{
    assert(forall|i: int| 0 <= i <= str.len() ==> {
        if i < bound {
            isNotPrefixPred(sub, str.subrange(i, str.len() as int))
        } else {
            // For i >= bound, sub.len() > str.len() - i, so prefix check fails
            let remaining = str.subrange(i, str.len() as int);
            sub.len() > remaining.len() && isNotPrefixPred(sub, remaining)
        }
    });
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str),
        !res <==> isNotSubstringPred(sub, str)
{
    if sub.len() > str.len() {
        proof {
            assert(forall|i: int| 0 <= i <= str.len() ==> {
                let substr = str.subrange(i, str.len() as int);
                sub.len() > substr.len() && isNotPrefixPred(sub, substr)
            });
            assert(isNotSubstringPred(sub, str));
        }
        return false;
    }
    
    let mut i: usize = 0;
    let bound: usize = str.len() - sub.len() + 1;
    while i < bound
        invariant 
            0 <= i <= bound,
            bound == str.len() - sub.len() + 1,
            sub.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int))
        decreases bound - i
    {
        let remaining_str = str.subrange(i as int, str.len() as int);
        
        if isPrefix(sub, remaining_str) {
            proof {
                assert(isPrefixPred(sub, remaining_str));
                lemma_substring_found(sub, str, i as int);
            }
            return true;
        }
        
        proof {
            assert(isNotPrefixPred(sub, remaining_str));
        }
        
        i += 1;
    }
    
    proof {
        lemma_no_substring(sub, str, bound as int);
    }
    
    false
}

}