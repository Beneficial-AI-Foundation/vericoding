use vstd::prelude::*;

verus! {

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
{
    assume(false);
    false
}



spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_substring_pred(sub, str),
        //!res <==> is_not_substring_pred(sub, str), // This postcondition follows from the above lemma.
{
    assume(false);
    false
}


spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 
        0 <= i1 <= str1.len() - k && 
        j1 == i1 + k && 
        is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 
        0 <= i1 <= str1.len() - k && 
        j1 == i1 + k ==> 
        is_not_substring_pred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
spec fn exists_match_in_str_at_k(k: nat, sub: Seq<char>, s: Seq<char>, upto: int) -> bool {
    exists|i: int|
        0 <= i < upto &&
        i <= s.len() - (k as int) &&
        s.subrange(i, i + (k as int)) == sub
}

spec fn exists_common_before(k: nat, s1: Seq<char>, s2: Seq<char>, upto1: int) -> bool {
    exists|i1: int|
        0 <= i1 < upto1 &&
        i1 <= s1.len() - (k as int) &&
        exists|i2: int|
            0 <= i2 &&
            i2 <= s2.len() - (k as int) &&
            s1.subrange(i1, i1 + (k as int)) == s2.subrange(i2, i2 + (k as int))
}
// </vc-helpers>

// <vc-spec>
fn have_common_k_substring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> have_common_k_substring_pred(k, str1, str2),
        //!found <==> have_not_common_k_substring_pred(k, str1, str2), // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    let n1: int = str1.len();
    let n2: int = str2.len();
    let k_int: int = k as int;

    if k_int > n1 || k_int > n2 {
        return false;
    }

    let mut found: bool = false;
    let mut match_i1: int = -1;
    let mut match_i2: int = -1;

    let mut i1: int = 0;
    while i1 <= n1 - k_int && !found
        invariant 0 <= i1 <= n1 - k_int + 1
        invariant (found ==> 0 <= match_i1 && match_i1 <= n1 - k_int && 0 <= match_i2 && match_i2 <= n2 - k_int &&
                   str1.subrange(match_i1, match_i1 + k_int) == str2.subrange(match_i2, match_i2 + k_int)))
        invariant (!found ==> match_i1 == -1 && match_i2 == -1)
        decreases n1 - k_int - i1 + 1
    {
        let sub: Seq<char> = str1.subrange(i1, i1 + k_int);

        let mut i2: int = 0;
        while i2 <= n2 - k_int && !found
            invariant 0 <= i2 <= n2 - k_int + 1
            invariant (found ==> 0 <= match_i1 && match_i1 <= n1 - k_int && 0 <= match_i2 && match_i2 <= n2 - k_int &&
                       str1.subrange(match_i1, match_i1 + k_int) == str2.subrange(match_i2, match_i2 + k_int)))
            invariant (!found ==> match_i1 == -1 && match_i2 == -1)
            decreases n2 - k_int - i2 + 1
        {
            if str2.subrange(i2, i2 + k_int) == sub {
                found = true;
                match_i1 = i1;
                match_i2 = i2;
            } else {
                i2 = i2 + 1;
            }
        }

        if !found {
            i1 = i1 + 1;
        }
    }

    proof {
        if found {
            // match_i1 and match_i2 were set when found became true
            assert(match_i1 != -1);
            assert(0 <= match_i1 && match_i1 <= n1 - k_int);
            assert(0 <= match_i2 && match_i2 <= n2 - k_int);
            assert(str1.subrange(match_i1, match_i1 + k_int) == str2.subrange(match_i2, match_i2 + k_int));

            // show existence required by have_common_k_substring_pred:
            // pick i1w = match_i1, j1w = match_i1 + k_int
            let i1w: int = match_i1;
            let j1w: int = match_i1 + k_int;
            assert(0 <= i1w && i1w <= n1 - k_int);
            assert(j1w == i1w + k_int);

            // show is_substring_pred(str1.subrange(i1w, j1w), str2)
            // pick i2w = match_i2 as witness for substring position in str2
            let i2w: int = match_i2;
            assert(0 <= i2w && i2w <= n2 - k_int);
            // show is_prefix_pred of the k-length substring against str2.subrange(i2w, n2)
            assert(is_prefix_pred(str1.subrange(i1w, j1w), str2.subrange(i2w, n2)));
            // therefore is_substring_pred holds
            assert(exists|ii: int| 0 <= ii <= n2 && is_prefix_pred(str1.subrange(i1w, j1w), str2.subrange(ii, n2)));

            // combine to satisfy have_common_k_substring_pred
            assert(exists|ai: int, aj: int|
                0 <= ai <= n1 - k_int &&
                aj == ai + k_int &&
                is_substring_pred(str1.subrange(ai, aj), str2)
            );
            assert(have_common_k_substring_pred(k, str1, str2));
        } else {
            // no match found
            assert(!have_common_k_substring_pred(k, str1, str2));
        }
    }

    found
}
// </vc-code>

fn main() {}

}