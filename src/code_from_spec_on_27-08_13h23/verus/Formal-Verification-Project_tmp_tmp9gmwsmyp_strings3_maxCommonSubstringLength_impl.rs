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
proof fn lemma_substring_implies_prefix(sub: Seq<char>, str: Seq<char>, i: int)
    requires
        0 <= i <= str.len() - sub.len(),
        str.subrange(i, i + sub.len()) == sub,
    ensures
        is_prefix_pred(sub, str.subrange(i, str.len() as int))
{
    assert(sub.len() <= str.subrange(i, str.len() as int).len());
    assert(sub == str.subrange(i, i + sub.len()));
    assert(str.subrange(i, i + sub.len()) == str.subrange(i, str.len() as int).subrange(0, sub.len()));
}

proof fn lemma_prefix_implies_substring(sub: Seq<char>, str: Seq<char>, i: int)
    requires
        0 <= i <= str.len(),
        is_prefix_pred(sub, str.subrange(i, str.len() as int)),
    ensures
        i <= str.len() - sub.len(),
        str.subrange(i, i + sub.len()) == sub
{
    assert(sub.len() <= str.subrange(i, str.len() as int).len());
    assert(sub == str.subrange(i, str.len() as int).subrange(0, sub.len()));
    assert(sub == str.subrange(i, i + sub.len()));
}

fn is_substring_at(sub: &Vec<char>, str: &Vec<char>, start: usize) -> (result: bool)
    requires
        start <= str.len(),
        sub.len() <= str.len() - start,
    ensures
        result == is_prefix_pred(sub@, str@.subrange(start as int, str.len() as int))
{
    if sub.len() == 0 {
        return true;
    }
    let mut j: usize = 0;
    while j < sub.len()
        invariant
            0 <= j <= sub.len(),
            start + j <= str.len(),
            forall|k: int| 0 <= k < j ==> sub@[k] == str@[start + k as usize],
    {
        if sub@[j] != str@[start + j] {
            return false;
        }
        j = j + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn max_common_substring_length(str1: &Vec<char>, str2: &Vec<char>) -> (len: usize)
    requires str1.len() <= str2.len()
    ensures 
        forall|k: int| len < k <= str1.len() ==> !have_common_k_substring_pred(k as nat, str1@, str2@),
        have_common_k_substring_pred(len as nat, str1@, str2@)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn max_common_substring_length(str1: &Vec<char>, str2: &Vec<char>) -> (len: usize)
    requires str1.len() <= str2.len()
    ensures
        forall|k: int| len < k <= str1.len() ==> !have_common_k_substring_pred(k as nat, str1@, str2@),
        len == 0 || have_common_k_substring_pred(len as nat, str1@, str2@)
{
    let mut high: usize = str1.len();
    let mut low: usize = 0;
    let mut result: usize = 0;
    let mut mid: usize;

    while low <= high
        invariant
            0 <= low <= high + 1,
            high <= str1.len(),
            result <= high,
            forall|k: int| result < k <= high ==> !have_common_k_substring_pred(k as nat, str1@, str2@),
            low <= result ==> have_common_k_substring_pred(result as nat, str1@, str2@),
        decreases high - low
    {
        mid = low + (high - low) / 2;
        if have_common_k_substring(mid, str1, str2) {
            result = mid;
            low = mid + 1;
        } else {
            if mid > 0 {
                high = mid - 1;
            } else {
                high = 0;
                low = 1;
            }
        }
    }
    result
}
// </vc-code>

fn main() {}

}