use vstd::prelude::*;

verus! {

spec fn is_substring(sub: Seq<char>, str: Seq<char>) -> bool
{
    exists|i: int| 0 <= i <= str.len() - sub.len() && str.subrange(i, i + sub.len()) == sub
}

spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool
{
    pre.len() <= str.len() && pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool
{
    pre.len() > str.len() || pre != str.subrange(0, pre.len() as int)
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool
{
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool
{
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool
{
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool
{
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

fn have_common_k_substring(k: usize, str1: &Vec<char>, str2: &Vec<char>) -> (found: bool)
    ensures found <==> have_common_k_substring_pred(k as nat, str1@, str2@)
{
    // Check that both strings are larger than k
    if k > str1.len() || k > str2.len() {
        return false;
    }
    // Initialize variables
    let mut i: usize = 0;
    let mut temp = false;

    // Don't want to exceed the bounds of str1 when checking for the element that is k entries away
    while i <= str1.len() - k
        invariant 
            // Invariant to stay within bounds
            0 <= i <= (str1.len() - k) + 1,
            // Invariant to show that when temp is true, it is a substring
            temp ==> 0 <= i <= (str1.len() - k) && is_substring_pred(str1@.subrange(i as int, (i + k) as int), str2@),
            // Invariant to show that when temp is false, it is not a substring
            !temp ==> (forall|m: int, n: int| (0 <= m < i && n == m + (k as int)) ==> is_not_substring_pred(str1@.subrange(m, n), str2@)),
        // Telling Verus that i is the value that is increasing
        decreases str1.len() - k - i
    {
        assume(false);

        // Get an index from the array position we are at to the array position that is k away and check the substring
        proof {
            let ghost_i = i as int;
            let ghost_k = k as int;
            let substr = str1@.subrange(ghost_i, ghost_i + ghost_k);
            temp = is_substring(substr, str2@);
        }
        if temp == true {
            return true;
        }
        i = i + 1;
    }
    false
}

// <vc-helpers>
spec fn is_prefix(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && pre.subrange(0, pre.len() as int) == str.subrange(0, pre.len() as int)
}

spec fn has_substring(sub: Seq<char>, s: Seq<char>) -> bool {
    exists|i: int| 
        0 <= i && (i + sub.len() as int) <= s.len() && is_prefix(sub, s.subrange(i, s.len() as int))
}

proof fn lemma_is_substring_equiv(sub: Seq<char>, s: Seq<char>) 
    ensures is_substring(sub, s) <==> has_substring(sub, s)
{
    assert(is_substring(sub, s)) == (exists|i: int| 0 <= i <= s.len() - sub.len() && s.subrange(i, i + sub.len()) == sub);
    assert(has_substring(sub, s)) == (exists|i: int| 0 <= i && (i + sub.len()) as int <= s.len() && is_prefix(sub, s.subrange(i, s.len() as int)));
    
    // Prove equivalence between is_prefix_pred and is_prefix
    assert forall|i: int| #![trigger s.subrange(i, s.len() as int)]
        is_prefix_pred(sub, s.subrange(i, s.len() as int)) <==> is_prefix(sub, s.subrange(i, s.len() as int)) by {
        assert(is_prefix_pred(sub, s.subrange(i, s.len() as int))) == (sub.len() <= s.subrange(i, s.len() as int).len() && sub == s.subrange(i, s.len() as int).subrange(0, sub.len() as int));
        assert(is_prefix(sub, s.subrange(i, s.len() as int))) == (sub.len() <= s.subrange(i, s.len() as int).len() && sub.subrange(0, sub.len() as int) == s.subrange(i, s.len() as int).subrange(0, sub.len() as int));
    }

    assert( (exists|i: int| 0 <= i <= s.len() && is_prefix_pred(sub, s.subrange(i, s.len() as int))) == 
            (exists|i: int| 0 <= i <= s.len() && is_prefix(sub, s.subrange(i, s.len() as int))) );
    
    assert(is_substring(sub, s)) == has_substring(sub, s) by {
        assert( (exists|i: int| 0 <= i <= s.len() - sub.len() && s.subrange(i, i + sub.len()) == sub) <==> 
                (exists|i: int| 0 <= i && (i + sub.len()) <= s.len() && is_prefix(sub, s.subrange(i, s.len() as int))) );
    }
}

proof fn lemma_is_not_substring_equiv(sub: Seq<char>, s: Seq<char>) 
    ensures is_not_substring_pred(sub, s) <==> !has_substring(sub, s)
{
    assert(is_not_substring_pred(sub, s)) == forall|i: int| 0 <= i <= s.len() ==> is_not_prefix_pred(sub, s.subrange(i, s.len() as int));
    assert(!has_substring(sub, s)) == forall|i: int| !(0 <= i && (i + sub.len()) as int <= s.len() && is_prefix(sub, s.subrange(i, s.len() as int)));

    assert forall|i: int| #![trigger s.subrange(i, s.len() as int)]
        is_not_prefix_pred(sub, s.subrange(i, s.len() as int)) <==> !is_prefix(sub, s.subrange(i, s.len() as int)) by {
        assert(is_not_prefix_pred(sub, s.subrange(i, s.len() as int))) == (sub.len() > s.subrange(i, s.len() as int).len() || sub != s.subrange(i, s.len() as int).subrange(0, sub.len() as int));
        assert(!is_prefix(sub, s.subrange(i, s.len() as int))) == !(sub.len() <= s.subrange(i, s.len() as int).len() && sub.subrange(0, sub.len() as int) == s.subrange(i, s.len() as int).subrange(0, sub.len() as int));
    }
    
    assert(is_not_substring_pred(sub, s) == forall|i: int| 0 <= i <= s.len() ==> !is_prefix(sub, s.subrange(i, s.len() as int)));
}

proof fn lemma_have_common_k_substring_equiv(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures have_common_k_substring_pred(k, str1, str2) <==>
            (exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && has_substring(str1.subrange(i1, j1), str2))
{
    assert(have_common_k_substring_pred(k, str1, str2)) == (exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2));
    assert(exists|i1: int, j1: int| #![trigger str1.subrange(i1, j1)] 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2))
        == (exists|i1: int, j1: int| #![trigger str1.subrange(i1, j1)] 0 <= i1 <= str1.len() - k && j1 == i1 + k && has_substring(str1.subrange(i1, j1), str2)) by {
        assert forall|sub: Seq<char>| #![trigger is_substring_pred(sub, str2)] is_substring_pred(sub, str2) <==> has_substring(sub, str2) by {
            lemma_is_substring_equiv(sub, str2);
        }
    }
}

proof fn lemma_have_not_common_k_substring_equiv(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures have_not_common_k_substring_pred(k, str1, str2) <==>
            (forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> !has_substring(str1.subrange(i1, j1), str2))
{
    assert(have_not_common_k_substring_pred(k, str1, str2)) == (forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2));
    assert(forall|i1: int, j1: int| #![trigger str1.subrange(i1, j1)] 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2))
        == (forall|i1: int, j1: int| #![trigger str1.subrange(i1, j1)] 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> !has_substring(str1.subrange(i1, j1), str2)) by {
        assert forall|sub: Seq<char>| #![trigger is_not_substring_pred(sub, str2)] is_not_substring_pred(sub, str2) <==> !has_substring(sub, str2) by {
            lemma_is_not_substring_equiv(sub, str2);
        }
    }
}

fn have_common_k_substring_v2(k: usize, str1: &Vec<char>, str2: &Vec<char>) -> (found: bool)
    ensures found <==> have_common_k_substring_pred(k as nat, str1@, str2@)
{
    if k == 0 {
        return true; // Empty string is always a common substring
    }
    if k > str1.len() || k > str2.len() {
        return false;
    }

    let mut i: usize = 0;

    proof {
        lemma_is_substring_equiv(Seq::empty(), str2@);
        lemma_is_not_substring_equiv(Seq::empty(), str2@); // Added for completeness, might not be strictly needed here.
        lemma_have_common_k_substring_equiv(k as nat, str1@, str2@);
        lemma_have_not_common_k_substring_equiv(k as nat, str1@, str2@);
    }
    
    while i <= str1.len() - k
        invariant 
            0 <= i <= (str1.len() - k) + 1,
            // For all previous indices, no common substring of length k was found
            forall|idx: int| 0 <= idx < i ==> !has_substring(str1@.subrange(idx as int, (idx + k) as int), str2@),
            // The predicate based on `has_substring`
            have_common_k_substring_pred(k as nat, str1@, str2@) == 
                (exists|i1: int, j1: int| i <= i1 <= str1.len() - k && j1 == i1 + k && has_substring(str1@.subrange(i1, j1), str2@)),
            str1.len() as int >= k as int,
            str2.len() as int >= k as int,
        decreases str1.len() - k - i
    {
        let current_substring_seq = str1@.subrange(i as int, (i + k) as int);
        
        proof {
            lemma_is_substring_equiv(current_substring_seq, str2@);
            lemma_is_not_substring_equiv(current_substring_seq, str2@);
        }

        if has_substring(current_substring_seq, str2@) {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn max_common_substring_length(str1: &Vec<char>, str2: &Vec<char>) -> (len: usize)
    requires str1.len() <= str2.len()
    ensures 
        forall|k: int| len < k <= str1.len() ==> !have_common_k_substring_pred(k as nat, str1@, str2@),
        have_common_k_substring_pred(len as nat, str1@, str2@)
// </vc-spec>
// <vc-code>
{
    let str1_len = str1.len();
    let str2_len = str2.len();

    if str1_len == 0 || str2_len == 0 {
        return 0; // No common substring possible
    }

    let mut low: usize = 0;
    let mut high: usize = str1_len; // Since str1_len <= str2_len, max possible common length is str1_len
    let mut result: usize = 0;

    while low <= high
        invariant
            0 <= low <= str1_len + 1,
            0 <= high <= str1_len, // high can be at most str1_len
            0 <= result <= str1_len,
            // If result is the current max, then there is a common substring of length `result`
            result == 0 || have_common_k_substring_pred(result as nat, str1@, str2@),
            // For any k > high, there is no common substring
            forall|k: int| #[trigger have_common_k_substring_pred(k as nat, str1@, str2@)] high < k <= str1.len() ==> !have_common_k_substring_pred(k as nat, str1@, str2@),
            // For any k such that result < k < low, there is no common substring
            forall|k: int| #[trigger have_common_k_substring_pred(k as nat, str1@, str2@)] result < k < low ==> !have_common_k_substring_pred(k as nat, str1@, str2@),
        decreases high - low
    {
        let mid = low + (high - low) / 2;

        if mid > str1_len { 
            high = str1_len;
            continue;
        }

        if mid == 0 {
            result = 0; 
            low = mid + 1;
            continue;
        }

        let found_common = have_common_k_substring_v2(mid, str1, str2);

        if found_common { // If a common substring of length `mid` is found
            result = mid; // This `mid` is a possible answer
            low = mid + 1; // Try to find a longer one
        } else { // No common substring of length `mid` found
            proof {
                assert forall|k_inner: int| #[trigger have_common_k_substring_pred(k_inner as nat, str1@, str2@)] mid == k_inner implies !have_common_k_substring_pred(k_inner as nat, str1@, str2@) by {
                    if mid == k_inner {
                    }
                }
            }
            high = mid - 1; // Look for a shorter one
        }
    }
    result
}
// </vc-code>

fn main() {}

}