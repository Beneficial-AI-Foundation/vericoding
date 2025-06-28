use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn haveCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int| 0 <= i1 && i1 + k <= str1.len() && 
        isSubstringPred(str1.subrange(i1, i1 + k), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int| 0 <= i1 && i1 + k <= str1.len() ==> 
        isNotSubstringPred(str1.subrange(i1, i1 + k), str2)
}

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i && i + sub.len() <= str.len() && isPrefixPred(sub, str.subrange(i, str.len()))
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i && i + sub.len() <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len()))
}

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
    if sub.len() == 0 {
        proof {
            assert(isPrefixPred(sub, str.subrange(0, str.len())));
            assert(isSubstringPred(sub, str)) by {
                assert(0 <= 0 && 0 + sub.len() <= str.len());
                assert(isPrefixPred(sub, str.subrange(0, str.len())));
            };
        }
        return true;
    }
    
    let mut i: usize = 0;
    while i + sub.len() <= str.len()
        invariant 
            0 <= i <= str.len(),
            forall|j: int| 0 <= j < i && j + sub.len() <= str.len() ==> isNotPrefixPred(sub, str.subrange(j, str.len()))
        decreases str.len() - i
    {
        if isPrefix(sub, str.subrange(i as int, str.len())) {
            proof {
                assert(isPrefixPred(sub, str.subrange(i as int, str.len())));
                assert(isSubstringPred(sub, str)) by {
                    assert(0 <= i && i + sub.len() <= str.len());
                };
            }
            return true;
        }
        proof {
            assert(isNotPrefixPred(sub, str.subrange(i as int, str.len())));
        }
        i += 1;
    }
    
    proof {
        assert(forall|j: int| 0 <= j < str.len() - sub.len() + 1 && j + sub.len() <= str.len() ==> 
            isNotPrefixPred(sub, str.subrange(j, str.len())));
        assert(!isSubstringPred(sub, str)) by {
            if isSubstringPred(sub, str) {
                assert(exists|k: int| 0 <= k && k + sub.len() <= str.len() && isPrefixPred(sub, str.subrange(k, str.len())));
                let k = choose|k: int| 0 <= k && k + sub.len() <= str.len() && isPrefixPred(sub, str.subrange(k, str.len()));
                assert(isNotPrefixPred(sub, str.subrange(k, str.len())));
                assert(false);
            }
        };
    }
    
    false
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> isPrefixPred(pre, str)
    ensures !res <==> isNotPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    if pre.len() == 0 {
        proof {
            assert(pre == str.subrange(0, 0));
            assert(isPrefixPred(pre, str));
        }
        return true;
    }
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> pre[j] == str[j]
        decreases pre.len() - i
    {
        if pre[i] != str[i] {
            proof {
                assert(pre != str.subrange(0, pre.len() as int)) by {
                    assert(pre[i as int] != str.subrange(0, pre.len() as int)[i as int]);
                };
                assert(isNotPrefixPred(pre, str));
            }
            return false;
        }
        i += 1;
    }
    
    proof {
        assert(pre.len() <= str.len());
        assert(pre =~= str.subrange(0, pre.len() as int)) by {
            assert(pre.len() == str.subrange(0, pre.len() as int).len());
            assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str.subrange(0, pre.len() as int)[j]) by {
                assert(forall|j: int| 0 <= j < pre.len() ==> str.subrange(0, pre.len() as int)[j] == str[j]);
            };
        };
        assert(isPrefixPred(pre, str));
    }
    
    true
}

fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
    if k == 0 {
        proof {
            let empty_seq: Seq<char> = Seq::empty();
            assert(isSubstringPred(empty_seq, str2));
            assert(haveCommonKSubstringPred(k, str1, str2)) by {
                if str1.len() > 0 {
                    assert(str1.subrange(0, 0) == empty_seq);
                    assert(0 <= 0 && 0 + k <= str1.len());
                    assert(isSubstringPred(str1.subrange(0, 0), str2));
                } else {
                    // str1 is empty, so there are no valid positions
                    assert(forall|i1: int| 0 <= i1 && i1 + k <= str1.len() ==> i1 == 0);
                    if exists|i1: int| 0 <= i1 && i1 + k <= str1.len() {
                        assert(0 <= 0 && 0 + k <= str1.len());
                        assert(str1.subrange(0, 0) == empty_seq);
                        assert(isSubstringPred(str1.subrange(0, 0), str2));
                    }
                }
            };
        }
        return true;
    }
    
    if k > str1.len() {
        proof {
            assert(!haveCommonKSubstringPred(k, str1, str2)) by {
                assert(forall|i1: int| !(0 <= i1 && i1 + k <= str1.len()));
            };
        }
        return false;
    }
    
    let mut i: usize = 0;
    while i + k <= str1.len()
        invariant 
            0 <= i <= str1.len(),
            k <= str1.len(),
            forall|j: int| 0 <= j < i && j + k <= str1.len() ==> 
                isNotSubstringPred(str1.subrange(j, j + k), str2)
        decreases str1.len() - i
    {
        let substring = str1.subrange(i as int, i as int + k as int);
        if isSubstring(substring, str2) {
            proof {
                assert(isSubstringPred(substring, str2));
                assert(haveCommonKSubstringPred(k, str1, str2)) by {
                    assert(0 <= i && i + k <= str1.len());
                    assert(str1.subrange(i as int, i as int + k as int) == substring);
                };
            }
            return true;
        }
        proof {
            assert(isNotSubstringPred(substring, str2));
            assert(isNotSubstringPred(str1.subrange(i as int, i as int + k as int), str2));
        }
        i += 1;
    }
    
    proof {
        assert(!haveCommonKSubstringPred(k, str1, str2)) by {
            if haveCommonKSubstringPred(k, str1, str2) {
                let witness = choose|i1: int| 0 <= i1 && i1 + k <= str1.len() && 
                    isSubstringPred(str1.subrange(i1, i1 + k), str2);
                assert(0 <= witness < str1.len() - k + 1);
                assert(isNotSubstringPred(str1.subrange(witness, witness + k), str2));
                assert(false);
            }
        };
    }
    
    false
}

fn maxCommonSubstringLength(str1: Seq<char>, str2: Seq<char>) -> (len: nat)
    requires str1.len() <= str2.len()
    ensures 
        (forall|k: nat| len < k && k <= str1.len() ==> !haveCommonKSubstringPred(k, str1, str2)),
        len == 0 || haveCommonKSubstringPred(len, str1, str2)
{
    let mut maxLen: nat = 0;
    let mut k: nat = 1;
    
    // Handle empty substring case - empty substring always exists
    proof {
        assert(haveCommonKSubstringPred(0, str1, str2));
    }
    
    while k <= str1.len()
        invariant 
            0 <= maxLen < k,
            1 <= k <= str1.len() + 1,
            forall|j: nat| maxLen < j < k ==> !haveCommonKSubstringPred(j, str1, str2),
            haveCommonKSubstringPred(maxLen, str1, str2)
        decreases str1.len() - k + 1
    {
        if haveCommonKSubstring(k, str1, str2) {
            proof {
                assert(haveCommonKSubstringPred(k, str1, str2));
            }
            maxLen = k;
        } else {
            proof {
                assert(!haveCommonKSubstringPred(k, str1, str2));
            }
        }
        k += 1;
    }
    
    proof {
        assert(forall|j: nat| maxLen < j <= str1.len() ==> !haveCommonKSubstringPred(j, str1, str2));
        assert(maxLen == 0 || haveCommonKSubstringPred(maxLen, str1, str2));
    }
    
    maxLen
}

}