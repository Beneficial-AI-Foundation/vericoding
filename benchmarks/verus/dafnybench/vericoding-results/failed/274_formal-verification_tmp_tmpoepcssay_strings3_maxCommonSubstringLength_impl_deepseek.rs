use vstd::prelude::*;

verus! {

spec fn is_substring(sub: Seq<char>, str: Seq<char>) -> bool 
    decreases str.len()
{
    if sub.len() == 0 {
        true
    } else if str.len() < sub.len() {
        false
    } else {
        (str.subrange(0, sub.len() as int) == sub) || is_substring(sub, str.subrange(1, str.len() as int))
    }
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
    exists|i: int| #![auto] 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| #![auto] 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| #![auto] 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| #![auto] 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures 
        found <==> have_common_k_substring_pred(k as nat, str1, str2),
        !found <==> have_not_common_k_substring_pred(k as nat, str1, str2),
{
    assume(false);
    false
}

// <vc-helpers>
proof fn is_substring_implies_pred(sub: Seq<char>, str: Seq<char>)
    ensures
        is_substring(sub, str) <==> is_substring_pred(sub, str),
    decreases str.len(),
{
    if sub.len() == 0 {
        assert(is_substring_pred(sub, str)) by {
            assert(is_prefix_pred(sub, str.subrange(0, str.len() as int)));
        }
    } else if str.len() < sub.len() {
        assert(is_not_substring_pred(sub, str)) by {
            assert forall|i: int| 0 <= i <= str.len() implies is_not_prefix_pred(sub, str.subrange(i, str.len() as int)) by {
                assert(str.subrange(i, str.len() as int).len() == (str.len() - i) < sub.len());
            }
        }
    } else {
        if str.subrange(0, sub.len() as int) == sub {
            assert(is_substring_pred(sub, str)) by {
                assert(is_prefix_pred(sub, str.subrange(0, str.len() as int)));
            }
        } else {
            is_substring_implies_pred(sub, str.subrange(1, str.len() as int));
            assert(is_substring_pred(sub, str) == is_substring_pred(sub, str.subrange(1, str.len() as int)));
        }
    }
}

proof fn have_common_k_substring_pred_equiv(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures
        have_common_k_substring_pred(k, str1, str2) == 
        (exists|i: int| 0 <= i <= str1.len() - k && is_substring_pred(str1.subrange(i, i + k), str2)),
{
}

proof fn have_not_common_k_substring_pred_equiv(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures
        have_not_common_k_substring_pred(k, str1, str2) == 
        (forall|i: int| 0 <= i <= str1.len() - k ==> is_not_substring_pred(str1.subrange(i, i + k), str2)),
{
}

proof fn lemma_subrange_len<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        s.subrange(i, j).len() == j - i,
{
}

proof fn lemma_subrange_empty<T>(s: Seq<T>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        s.subrange(i, i) == Seq::empty(),
{
}

fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures 
        found <==> have_common_k_substring_pred(k as nat, str1, str2),
        !found <==> have_not_common_k_substring_pred(k as nat, str1, str2),
{
    let mut i: int = 0;
    let k_int = k as int;
    let str1_len = str1.len() as int;
    let str2_len = str2.len() as int;
    
    while i <= str1_len - k_int
        invariant
            0 <= i <= str1_len - k_int + 1,
            forall|j: int| 0 <= j < i ==> is_not_substring_pred(str1.subrange(j, j + k_int), str2),
    {
        let substr = str1.subrange(i, i + k_int);
        let mut found_sub: bool = false;
        let mut pos: int = 0;
        
        while pos <= str2_len - k_int
            invariant
                0 <= pos <= str2_len - k_int + 1,
                forall|p: int| 0 <= p < pos ==> !is_prefix_pred(substr, str2.subrange(p, str2_len)),
                found_sub == (exists|p: int| 0 <= p < pos && is_prefix_pred(substr, str2.subrange(p, str2_len))),
        {
            if is_prefix_pred(substr, str2.subrange(pos, str2_len)) {
                found_sub = true;
                break;
            }
            pos += 1;
        }
        
        if found_sub {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn max_common_substring_length(str1: Seq<char>, str2: Seq<char>) -> (len: usize)
    requires str1.len() <= str2.len(),
    ensures 
        forall|k: nat| #![auto] len < k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2),
        have_common_k_substring_pred(len as nat, str1, str2),
// </vc-spec>
// <vc-code>
{
    let mut max_len: usize = 0;
    
    proof {
        is_substring_implies_pred(Seq::<char>::empty(), str2);
    }
    
    let mut i: usize = 0;
    while i <= str1.len()
        invariant
            0 <= i <= str1.len() + 1,
            forall|k: nat| max_len < k <= str1.len() ==> 
                !have_common_k_substring_pred(k, str1.subrange(0, i as int), str2),
            have_common_k_substring_pred(max_len as nat, str1.subrange(0, i as int), str2),
    {
        if i < str1.len() {
            let mut j: usize = i + 1;
            while j <= str1.len()
                invariant
                    i < j <= str1.len() + 1,
                    forall|k: nat| max_len < k <= (j - i) ==> 
                        !have_common_k_substring_pred(k, str1.subrange(i as int, j as int), str2),
                    have_common_k_substring_pred(max_len as nat, str1.subrange(i as int, j as int), str2),
            {
                let substr_len = j - i;
                
                if substr_len > 0 {
                    let substr = str1.subrange(i as int, j as int);
                    let found = have_common_k_substring(substr_len, substr, str2);
                    
                    proof {
                        have_common_k_substring_pred_equiv(substr_len as nat, substr, str2);
                        is_substring_implies_pred(substr, str2);
                    }
                    
                    if found {
                        max_len = if max_len < substr_len { substr_len } else { max_len };
                    }
                }
                j += 1;
            }
        }
        i += 1;
    }
    
    max_len
}
// </vc-code>

fn main() {
}

}