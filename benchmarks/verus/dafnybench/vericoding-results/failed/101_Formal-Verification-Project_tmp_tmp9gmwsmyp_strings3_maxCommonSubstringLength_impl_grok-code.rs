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
pub fn is_substring_of(sub: &Vec<char>, str: &Vec<char>) -> (result: bool)
    requires sub@.len() == sub.len() as int,
        str@.len() == str.len() as int
    ensures result <==> is_substring(sub@, str@)
    ensures result <==> is_substring_pred(sub@, str@)
{
    if sub.len() > str.len() {
        return false;
    }
    let mut j: usize = 0;
    while j <= str.len() - sub.len()
        invariant 0 <= j <= str.len() - sub.len() + 1,
            forall |jj: int| 0 <= jj < j ==> !is_prefix_pred(sub@, str@.subrange(jj as int, str@.len() as int))
    {
        let mut equal = true;
        let mut p: usize = 0;
        while p < sub.len()
            invariant 0 <= p <= sub.len(),
                equal ==> forall |pp: int| 0 <= pp < p ==> sub@[pp as int] == str@[(j + pp) as int],
                p == sub.len() || !equal ==> equal == false
        {
            if sub[p] != str[j + p] {
                equal = false;
                break;
            }
            p = p + 1;
        }
        if equal {
            return true;
        }
        j = j + 1;
    }
    false
}

pub fn have_common_k_substring(k: usize, str1: &Vec<char>, str2: &Vec<char>) -> (found: bool)
    ensures found <==> have_common_k_substring_pred(k as nat, str1@, str2@)
{
    if k == 0 {
        return true;
    }
    if k > str1.len() || k > str2.len() {
        return false;
    }
    let mut i: usize = 0;
    let mut temp = false;
    while i <= str1.len() - k
        invariant 0 <= i <= (str1.len() - k) + 1,
            temp ==> 0 <= i <= (str1.len() - k) && is_substring_pred(str1@.subrange(i as int, (i + k) as int), str2@),
            !temp ==> (forall |m: int| (0 <= m < i) ==> is_not_substring_pred(str1@.subrange(m as int, (m + k) as int), str2@))
        decreases str1.len() - k - i
    {
        let sub_vec = &str1[i..i + k];
        assert(sub_vec@ == str1@.subrange(i as int, (i + k) as int));
        temp = is_substring_of(sub_vec, str2);
        if temp {
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
        return 0;
    }
    let mut low: usize = 0;
    let mut high: usize = str1.len();
    let mut result: usize = 0;
    while low <= high
        invariant 0 <= low <= high + 1,
            high <= str1.len(),
            result == 0 || have_common_k_substring_pred(result as nat, str1@, str2@),
            forall |k: int| 0 <= k < result || result < k <= str1.len() as int ==> !have_common_k_substring_pred(k as nat, str1@, str2@)
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if have_common_k_substring(mid, str1, str2) {
            result = mid;
            proof {
                if let Some(next) = mid.checked_add(1) {
                    low = next;
                } else {
                    low = high + 1; // to exit
                }
            }
        } else {
            high = mid - 1;
        }
    }
    result
}
// </vc-code>

fn main() {}

}