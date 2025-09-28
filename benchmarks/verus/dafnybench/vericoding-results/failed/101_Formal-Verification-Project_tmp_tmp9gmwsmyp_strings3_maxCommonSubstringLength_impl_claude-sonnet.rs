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
proof fn lemma_have_common_decreasing(str1: Seq<char>, str2: Seq<char>, k1: nat, k2: nat)
    requires k1 <= k2, have_common_k_substring_pred(k2, str1, str2)
    ensures have_common_k_substring_pred(k1, str1, str2)
{
    if k1 == 0 {
        assert(str1.subrange(0, 0) == Seq::<char>::empty());
        assert(is_substring_pred(Seq::<char>::empty(), str2));
        assert(have_common_k_substring_pred(0, str1, str2));
    } else {
        let i1: int = choose|i1: int| {
            let j1 = i1 + k2;
            0 <= i1 <= str1.len() - k2 && j1 == i1 + k2 && is_substring_pred(str1.subrange(i1, j1), str2)
        };
        let j1 = i1 + k2;
        assert(0 <= i1 <= str1.len() - k2);
        assert(is_substring_pred(str1.subrange(i1, j1), str2));
        
        let substr_k1 = str1.subrange(i1, i1 + k1);
        assert(substr_k1 == str1.subrange(i1, j1).subrange(0, k1 as int));
        
        let pos: int = choose|pos: int| {
            0 <= pos <= str2.len() && is_prefix_pred(str1.subrange(i1, j1), str2.subrange(pos, str2.len() as int))
        };
        
        assert(is_prefix_pred(substr_k1, str2.subrange(pos, str2.len() as int)));
        assert(is_substring_pred(substr_k1, str2));
        assert(have_common_k_substring_pred(k1, str1, str2));
    }
}

proof fn lemma_empty_substring(str: Seq<char>)
    ensures is_substring_pred(Seq::<char>::empty(), str)
{
    assert(is_prefix_pred(Seq::<char>::empty(), str.subrange(0, str.len() as int)));
    assert(is_substring_pred(Seq::<char>::empty(), str));
}

fn check_substring_at_position(str1: &Vec<char>, str2: &Vec<char>, i: usize, k: usize) -> (result: bool)
    requires 
        i + k <= str1.len(),
        k <= str2.len()
    ensures 
        result <==> is_substring_pred(str1@.subrange(i as int, (i + k) as int), str2@)
{
    let mut j = 0;
    while j <= str2.len() - k
        invariant 
            0 <= j <= (str2.len() - k) + 1,
            forall|pos: int| 0 <= pos < j ==> !is_prefix_pred(str1@.subrange(i as int, (i + k) as int), str2@.subrange(pos, str2.len() as int))
        decreases str2.len() - k - j
    {
        let mut matches = true;
        let mut l = 0;
        while l < k
            invariant 
                0 <= l <= k,
                matches <==> (forall|m: int| 0 <= m < l ==> str1@[i + m] == str2@[j + m])
            decreases k - l
        {
            if str1[i + l] != str2[j + l] {
                matches = false;
                break;
            }
            l = l + 1;
        }
        if matches {
            proof {
                assert(forall|m: int| 0 <= m < k ==> str1@[i + m] == str2@[j + m]);
                assert(str1@.subrange(i as int, (i + k) as int) == str2@.subrange(j as int, (j + k) as int));
                assert(is_prefix_pred(str1@.subrange(i as int, (i + k) as int), str2@.subrange(j as int, str2.len() as int)));
                assert(is_substring_pred(str1@.subrange(i as int, (i + k) as int), str2@));
            }
            return true;
        }
        j = j + 1;
    }
    proof {
        assert(forall|pos: int| 0 <= pos <= str2.len() - k ==> !is_prefix_pred(str1@.subrange(i as int, (i + k) as int), str2@.subrange(pos, str2.len() as int)));
        assert(!is_substring_pred(str1@.subrange(i as int, (i + k) as int), str2@));
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
            lemma_empty_substring(str2@);
        }
        return 0;
    }
    
    let mut k = str1.len();
    
    while k > 0
        invariant 
            0 <= k <= str1.len(),
            forall|m: int| k < m <= str1.len() ==> !have_common_k_substring_pred(m as nat, str1@, str2@)
        decreases k
    {
        if k > str2.len() {
            k = k - 1;
            continue;
        }
        
        let mut i = 0;
        let mut found = false;
        
        while i <= str1.len() - k && !found
            invariant 
                0 <= i <= (str1.len() - k) + 1,
                !found ==> (forall|m: int| 0 <= m < i ==> !is_substring_pred(str1@.subrange(m, m + k as int), str2@))
            decreases str1.len() - k - i
        {
            found = check_substring_at_position(str1, str2, i, k);
            if !found {
                i = i + 1;
            }
        }
        
        if found {
            proof {
                assert(exists|m: int| 0 <= m < i + 1 && is_substring_pred(str1@.subrange(m, m + k as int), str2@));
                assert(have_common_k_substring_pred(k as nat, str1@, str2@));
            }
            return k;
        }
        k = k - 1;
    }
    
    proof {
        lemma_empty_substring(str2@);
    }
    0
}
// </vc-code>

fn main() {}

}