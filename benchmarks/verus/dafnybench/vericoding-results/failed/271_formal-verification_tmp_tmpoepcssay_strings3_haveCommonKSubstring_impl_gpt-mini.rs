use vstd::prelude::*;

verus! {

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str),
{
    assume(false);
    true
}



spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int))
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str),
        res ==> isSubstringPred(sub, str),
        // ensures  !res ==> !isSubstringPred(sub, str)
        isSubstringPred(sub, str) ==> res,
        isSubstringPred(sub, str) ==> res,
        !res <==> isNotSubstringPred(sub, str), // This postcondition follows from the above lemma.
{
    assume(false);
    true
}



spec fn haveCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && isSubstringPred(str1.subrange(i1, j1), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> isNotSubstringPred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
proof fn subrange_subrange<T>(s: Seq<T>, a: int, b: int, c: int, d: int)
    requires 0 <= a && a <= b && b <= s.len()
    requires 0 <= c && c <= d && d <= b - a
    ensures s.subrange(a, b).subrange(c, d) == s.subrange(a + c, a + d)
{
    // lengths
    assert((s.subrange(a, b).subrange(c, d)).len() == d - c);
    assert((s.subrange(a + c, a + d)).len() == d - c);
    // pointwise equality
    assert(forall|t: int|
        0 <= t && t < d - c ==>
            s.subrange(a, b).subrange(c, d)@[t] == s.subrange(a + c, a + d)@[t]
    );
    // conclude equality
    assert(s.subrange(a, b).subrange(c, d) == s.subrange(a + c, a + d));
}

proof fn subrange_index<T>(s: Seq<T>, a: int, b: int, t: int)
    requires 0 <= a && a <= b && b <= s.len()
    requires 0 <= t && t < b - a
    ensures s.subrange(a, b)@[t] == s@[a + t]
{
    // By definition of subrange indexing this holds; assert to help verifier
    assert(s.subrange(a, b)@[t] == s@[a + t]);
}

proof fn equal_subrange_implies_isPrefix(s: Seq<char>, j: int, k: int, sub: Seq<char>)
    requires 0 <= j && j + k <= s.len()
    requires sub.len() == k
    requires sub == s.subrange(j, j + k)
    ensures isPrefixPred(sub, s.subrange(j, s.len()))
{
    // s.subrange(j, s.len()).subrange(0, k) == s.subrange(j, j+k)
    subrange_subrange(s, j, s.len(), 0, k);
    assert(s.subrange(j, s.len()).subrange(0, k) == s.subrange(j, j + k));
    assert(sub == s.subrange(j, s.len()).subrange(0, sub.len()));
    // first conjunct of isPrefixPred: pre.len() <= str.len()
    assert(sub.len() <= s.subrange(j, s.len()).len());
    // second conjunct: sub == str.subrange(0, sub.len()) holds by above
    assert(isPrefixPred(sub, s.subrange(j, s.len())));
}

proof fn equal_subrange_implies_isSubstring(s: Seq<char>, j: int, k: int, sub: Seq<char>)
    requires 0 <= j && j + k <= s.len()
    requires sub.len() == k
    requires sub == s.subrange(j, j + k)
    ensures isSubstringPred(sub, s)
{
    equal_subrange_implies_isPrefix(s, j, k, sub);
    assert(isPrefixPred(sub, s.subrange(j, s.len())));
    assert(isSubstringPred(sub, s));
}

proof fn unequal_subrange_implies_isNotPrefix(s: Seq<char>, j: int, k: int, sub: Seq<char>)
    requires 0 <= j && j + k <= s.len()
    requires sub.len() == k
    requires sub != s.subrange(j, j + k)
    ensures isNotPrefixPred(sub, s.subrange(j, s.len()))
{
    // s.subrange(j, s.len()).subrange(0, k) == s.subrange(j, j + k)
    subrange_subrange(s, j, s.len(), 0, k);
    assert(s.subrange(j, s.len()).subrange(0, k) == s.subrange(j, j + k));
    // thus sub != s.subrange(j, s.len()).subrange(0, sub.len())
    assert(sub != s.subrange(j, s.len()).subrange(0, sub.len()));
    // so second disjunct of isNotPrefixPred holds
    assert(isNotPrefixPred(sub, s.subrange(j, s.len())));
}
// </vc-helpers>

// <vc-spec>
fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> haveCommonKSubstringPred(k, str1, str2),
        !found <==> haveNotCommonKSubstringPred(k, str1, str2), // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    let n1 = str1.len();
    let n2 = str2.len();
    let int_k = k as int;

    if int_k > n1 {
        return false;
    }

    let mut found: bool = false;
    let mut i1: int = 0;
    let mut matched_i: int = 0;
    let mut matched_j: int = 0;

    while i1 <= n1 - int_k && !found
        invariant 0 <= i1 && i1 <= n1 - int_k + 1
        invariant found ==> 0 <= matched_i && matched_i <= n1 - int_k && 0 <= matched_j && matched_j <= n2 - int_k && str2.subrange(matched_j, matched_j + int_k) == str1.subrange(matched_i, matched_i + int_k)
        invariant !found ==> forall|ii: int| 0 <= ii && ii < i1 && ii <= n1 - int_k ==> isNotSubstringPred(str1.subrange(ii, ii + int_k), str2)
    {
        let sub = str1.subrange(i1, i1 + int_k);

        // inner loop over str2 positions
        let mut j: int = 0;
        while j <= n2 - int_k && !found
            invariant 0 <= j && j <= n2 - int_k + 1
            invariant found ==> 0 <= matched_i && matched_i <= n1 - int_k && 0 <= matched_j && matched_j <= n2 - int_k && str2.subrange(matched_j, matched_j + int_k) == str1.subrange(matched_i, matched_i + int_k)
            invariant !found ==> forall|jj: int| 0 <= jj && jj < j && jj <= n2 - int_k ==> str2.subrange(jj, jj + int_k) != sub
        {
            if str2.subrange(j, j + int_k) == sub {
                // record match
                found = true;
                matched_i = i1;
                matched_j = j;
            } else {
                j = j + 1;
            }
        }

        if !found {
            i1 = i1 + 1;
        }
    }

    // Now prove the postconditions
    if found {
        // matched_i and matched_j witness the existential in haveCommonKSubstringPred
        assert(0 <= matched_i && matched_i <= n1 - int_k);
        assert(0 <= matched_j && matched_j <= n2 - int_k);
        // str2.subrange(matched_j, matched_j + k) == str1.subrange(matched_i, matched_i + k)
        assert(str2.subrange(matched_j, matched_j + int_k) == str1.subrange(matched_i, matched_i + int_k));
        // from equality we get isSubstringPred(str1.subrange(matched_i, matched_i + k), str2)
        equal_subrange_implies_isSubstring(str2, matched_j, int_k, str1.subrange(matched_i, matched_i + int_k));
        // produce existential
        proof {
            reveal haveCommonKSubstringPred;
        }
        return true;
    } else {
        // Show forall i1 in range implies isNotSubstringPred
        // From loop invariant we have forall ii < i1 => isNotSubstringPred(...). At loop exit, either i1 > n1 - k or found (but found is false), so i1 > n1 - k.
        // So for any ii with 0 <= ii && ii <= n1 - k, we have ii < i1, hence isNotSubstringPred holds.
        assert(i1 > n1 - int_k || found);
        assert(!found);
        // derive the universal claim
        assert(forall|ii: int| 0 <= ii && ii <= n1 - int_k ==> isNotSubstringPred(str1.subrange(ii, ii + int_k), str2));
        proof {
            // no additional steps needed; assertion above follows from loop invariant and exit condition
        }
        return false;
    }
}
// </vc-code>

fn main() {}

}