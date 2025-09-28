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
fn is_subslice_in_str2(str1: &Vec<char>, start: usize, len: usize, str2: &Vec<char>) -> (found: bool)
    requires start + len <= str1.len()
    ensures found <==> is_substring(str1@.subrange(start as int, start as int + len as int), str2@)
{
    if len == 0 {
        return true;
    }
    let mut i = 0;
    while i <= str2.len() - len
        invariant 
            0 <= i <= str2.len() - len + 1,
            forall|m: int| 0 <= m < i ==> !is_prefix_pred(str1@.subrange(start as int, start as int + len as int), str2@.subrange(m, str2.len() as int))
        decreases str2.len() - len - i
    {
        let mut j = 0;
        let mut match_found = true;
        while j < len
            invariant 
                0 <= j <= len,
                match_found ==> (forall|k: int| 0 <= k < j ==> str1@[start as int + k] == str2@[i + k]),
                !match_found ==> (exists|k: int| 0 <= k < j && str1@[start as int + k] != str2@[i + k])
            decreases len - j
        {
            if str1[start+j] != str2[i+j] {
                match_found = false;
                break;
            }
            j += 1;
        }
        if match_found {
            return true;
        }
        i += 1;
    }
    false
}

spec fn common_substring_length_at_most(str1: Seq<char>, str2: Seq<char>, max_len: int) -> (max_common: usize)
    ensures max_common <= max_len as usize
{
    if max_len < 1 {
        0
    } else {
        if have_common_k_substring_pred(max_len as nat, str1, str2) {
            common_substring_length_at_most(str1, str2, max_len - 1) + 1_usize
        } else {
            common_substring_length_at_most(str1, str2, max_len - 1)
        }
    }
}

proof fn common_substring_length_at_most_property(str1: Seq<char>, str2: Seq<char>, max_len: int)
    ensures 
        forall|k: int| common_substring_length_at_most(str1, str2, max_len) < k <= max_len ==> !have_common_k_substring_pred(k as nat, str1, str2)
{
    if max_len < 1 {
    } else {
        let rec_result = common_substring_length_at_most(str1, str2, max_len - 1);
        common_substring_length_at_most_property(str1, str2, max_len - 1);
        
        if have_common_k_substring_pred(max_len as nat, str1, str2) {
            let res = (rec_result as int) + 1;
            assert forall|k: int| res < k <= max_len implies !have_common_k_substring_pred(k as nat, str1, str2) by {
                if max_len == k {
                    assert(!have_common_k_substring_pred(k as nat, str1, str2));
                } else {
                    assert((rec_result as int) < k);
                }
            }
        } else {
            let rec_int = rec_result as int;
            assert forall|k: int| rec_int < k <= max_len implies !have_common_k_substring_pred(k as nat, str1, str2) by {
                if max_len == k {
                } else {
                    assert(rec_int < k);
                }
            }
        }
    }
}

proof fn common_substring_length_at_most_achieved(str1: Seq<char>, str2: Seq<char>, max_len: int)
    ensures have_common_k_substring_pred(common_substring_length_at_most(str1, str2, max_len) as nat, str1, str2)
{
    if max_len < 1 {
        assert(common_substring_length_at_most(str1, str2, max_len) == 0);
        assert(!have_common_k_substring_pred(0 as nat, str1, str2));
        assert(false);
    } else {
        let rec_result = common_substring_length_at_most(str1, str2, max_len - 1);
        common_substring_length_at_most_achieved(str1, str2, max_len - 1);
        if have_common_k_substring_pred(max_len as nat, str1, str2) {
            let res = (rec_result as int) + 1;
            assert(have_common_k_substring_pred(rec_result as nat, str1, str2));
        }
    }
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
    if str1.len() == 0 || str2.len() == 0 {
        return 0;
    }
    let max_possible_len = str1.len();
    let mut low = 0;
    let mut high = max_possible_len;
    let mut result = 0;
    
    while low <= high
        invariant 
            0 <= low && high <= max_possible_len,
            result == common_substring_length_at_most(str1@, str2@, max_possible_len as int),
            forall|k: int| (result as int) < k <= (max_possible_len as int) ==> !have_common_k_substring_pred(k as nat, str1@, str2@),
            have_common_k_substring_pred(result as nat, str1@, str2@) || result == 0
        decreases high - low
    {
        let mid = low + ((high - low) / 2);
        if mid == 0 {
            low = 1;
            continue;
        }
        let found = is_subslice_in_str2(&str1, 0, mid, &str2);
        if found {
            result = mid;
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    proof {
        common_substring_length_at_most_property(str1@, str2@, max_possible_len as int);
        common_substring_length_at_most_achieved(str1@, str2@, max_possible_len as int);
    }
    result
}
// </vc-code>

fn main() {}

}