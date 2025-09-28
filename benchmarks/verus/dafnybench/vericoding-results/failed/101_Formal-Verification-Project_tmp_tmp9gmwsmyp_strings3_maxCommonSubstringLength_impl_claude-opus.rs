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
proof fn lemma_no_common_substring_implies_smaller(k: nat, str1: Seq<char>, str2: Seq<char>)
    requires
        !have_common_k_substring_pred(k as nat, str1, str2),
        k > 0,
    ensures
        forall|j: nat| k <= j <= str1.len() ==> !have_common_k_substring_pred(j as nat, str1, str2),
{
    assert forall|j: nat| k <= j <= str1.len() implies !have_common_k_substring_pred(j as nat, str1, str2) by {
        if k <= j <= str1.len() {
            assert forall|i1: int, j1: int| 0 <= i1 <= str1.len() - j && j1 == i1 + j implies 
                is_not_substring_pred(str1.subrange(i1, j1), str2) by {
                if 0 <= i1 <= str1.len() - j && j1 == i1 + j {
                    assert(0 <= i1 <= str1.len() - k);
                    let sub_k = str1.subrange(i1, i1 + k);
                    assert(is_not_substring_pred(sub_k, str2));
                    
                    let sub_j = str1.subrange(i1, j1);
                    assert forall|i2: int| 0 <= i2 <= str2.len() implies 
                        is_not_prefix_pred(sub_j, str2.subrange(i2, str2.len() as int)) by {
                        if 0 <= i2 <= str2.len() {
                            if sub_j.len() <= str2.len() - i2 && sub_j == str2.subrange(i2, i2 + sub_j.len()) {
                                assert(sub_k == str1.subrange(i1, i1 + k));
                                assert(sub_k == sub_j.subrange(0, k as int));
                                assert(sub_k == str2.subrange(i2, i2 + k));
                                assert(is_prefix_pred(sub_k, str2.subrange(i2, str2.len() as int)));
                                assert(false);
                            }
                        }
                    }
                }
            }
        }
    }
}

fn is_substring_exec(sub: &[char], str: &[char]) -> (result: bool)
    ensures result == is_substring(sub@, str@)
{
    if sub.len() > str.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= str.len() - sub.len()
        invariant 
            0 <= i <= str.len() - sub.len() + 1,
            forall|j: int| 0 <= j < i ==> str@.subrange(j, j + sub@.len() as int) != sub@,
    {
        let mut j: usize = 0;
        let mut matches = true;
        
        while j < sub.len()
            invariant
                0 <= j <= sub.len(),
                i <= str.len() - sub.len(),
                matches ==> forall|k: int| 0 <= k < j ==> sub@[k] == str@[i as int + k],
                !matches ==> exists|k: int| 0 <= k < j && sub@[k] != str@[i as int + k],
        {
            if sub[j] != str[i + j] {
                matches = false;
                break;
            }
            j = j + 1;
        }
        
        if matches {
            assert(str@.subrange(i as int, i as int + sub@.len() as int) == sub@);
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
    if str1.len() == 0 {
        proof {
            assert forall|k: int| 0 < k <= str1.len() implies 
                !have_common_k_substring_pred(k as nat, str1@, str2@) by {}
            assert(have_common_k_substring_pred(0 as nat, str1@, str2@)) by {
                let empty = str1@.subrange(0, 0);
                assert(is_substring_pred(empty, str2@)) by {
                    assert(is_prefix_pred(empty, str2@.subrange(0, str2@.len() as int)));
                }
            }
        }
        return 0;
    }
    
    let mut low: usize = 0;
    let mut high: usize = str1.len();
    let mut result: usize = 0;
    
    proof {
        assert(have_common_k_substring_pred(0 as nat, str1@, str2@)) by {
            let empty = str1@.subrange(0, 0);
            assert(is_substring_pred(empty, str2@)) by {
                assert(is_prefix_pred(empty, str2@.subrange(0, str2@.len() as int)));
            }
        }
    }
    
    while low <= high
        invariant
            0 <= low <= str1.len() + 1,
            0 <= high <= str1.len(),
            0 <= result <= str1.len(),
            low <= high + 1,
            forall|k: int| high < k <= str1.len() ==> !have_common_k_substring_pred(k as nat, str1@, str2@),
            have_common_k_substring_pred(result as nat, str1@, str2@),
            result <= high,
    {
        let mid = low + (high - low) / 2;
        
        if have_common_k_substring(mid, str1, str2) {
            result = mid;
            if mid < str1.len() {
                low = mid + 1;
            } else {
                break;
            }
        } else {
            if mid > 0 {
                high = mid - 1;
                proof {
                    lemma_no_common_substring_implies_smaller(mid as nat, str1@, str2@);
                }
            } else {
                break;
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}

}