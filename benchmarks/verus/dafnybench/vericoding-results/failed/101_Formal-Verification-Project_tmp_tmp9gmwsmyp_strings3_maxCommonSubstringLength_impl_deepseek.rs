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
proof fn lemma_substring_pred_equivalence(sub: Seq<char>, str: Seq<char>)
    ensures
        is_substring_pred(sub, str) <==> is_substring(sub, str),
    decreases sub.len()
{
    reveal_with_fuel(is_substring, 2);
    reveal_with_fuel(is_substring_pred, 2);
    reveal_with_fuel(is_prefix_pred, 2);
}

proof fn lemma_not_substring_pred_equivalence(sub: Seq<char>, str: Seq<char>)
    ensures
        is_not_substring_pred(sub, str) <==> !is_substring(sub, str),
    decreases sub.len()
{
    lemma_substring_pred_equivalence(sub, str);
    reveal_with_fuel(is_not_substring_pred, 1);
}

proof fn lemma_common_k_substring_has_substring(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures
        have_common_k_substring_pred(k, str1, str2) ==>
        exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring(str1.subrange(i1, j1), str2),
    decreases k
{
    reveal_with_fuel(have_common_k_substring_pred, 1);
    if have_common_k_substring_pred(k, str1, str2) {
        assert forall|i: int, j: int| 0 <= i <= str1.len() - k && j == i + k implies #[trigger] is_substring_pred(str1.subrange(i, j), str2) by {
            lemma_substring_pred_equivalence(str1.subrange(i, j), str2);
        };
    }
}

proof fn lemma_not_common_k_substring_no_substring(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures
        have_not_common_k_substring_pred(k, str1, str2) ==>
        forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> !is_substring(str1.subrange(i1, j1), str2),
    decreases k
{
    reveal_with_fuel(have_not_common_k_substring_pred, 1);
    if have_not_common_k_substring_pred(k, str1, str2) {
        assert forall|i: int, j: int| 0 <= i <= str1.len() - k && j == i + k implies #[trigger] is_not_substring_pred(str1.subrange(i, j), str2) by {
            lemma_not_substring_pred_equivalence(str1.subrange(i, j), str2);
        };
    }
}

proof fn check_substring_proof(substr: Seq<char>, str2: Seq<char>) -> (b: bool)
    ensures b == is_substring(substr, str2)
    decreases substr.len()
{
    reveal_with_fuel(is_substring, 2);
    is_substring(substr, str2)
}

spec fn is_substring_decreases() -> bool 
    decreases 1
{
    true
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
    let mut low: usize = 0;
    let mut high: usize = str1.len();
    let mut result: usize = 0;
    
    proof {
        reveal_with_fuel(is_substring_decreases, 1);
    }
    
    while low <= high
        invariant
            0 <= low <= high <= str1.len() + 1,
            result <= str1.len(),
            forall|k: int| result < k <= str1.len() ==> !have_common_k_substring_pred(k as nat, str1@, str2@),
            have_common_k_substring_pred(result as nat, str1@, str2@),
        decreases high - low
    {
        if low > high {
            break;
        }
        
        let mid = low + (high - low) / 2;
        let has_common = have_common_k_substring(mid, str1, str2);
        
        proof {
            lemma_common_k_substring_has_substring(mid as nat, str1@, str2@);
            lemma_not_common_k_substring_no_substring(mid as nat, str1@, str2@);
        }
        
        if has_common {
            result = mid;
            low = mid + 1;
        } else {
            if mid > 0 {
                high = mid - 1;
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