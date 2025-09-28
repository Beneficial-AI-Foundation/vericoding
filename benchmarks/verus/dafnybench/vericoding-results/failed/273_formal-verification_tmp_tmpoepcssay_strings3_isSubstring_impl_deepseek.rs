use vstd::prelude::*;

verus! {

spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
{
    assume(false);
    true
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() as int - k as int && j1 == i1 + k as int && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() as int - k as int && j1 == i1 + k as int ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
proof fn is_prefix_implies_or_not(pre: Seq<char>, str: Seq<char>)
    ensures
        is_prefix_pred(pre, str) || is_not_prefix_pred(pre, str),
{
}

proof fn is_substring_implies_or_not(sub: Seq<char>, str: Seq<char>)
    ensures
        is_substring_pred(sub, str) || is_not_substring_pred(sub, str),
{
    assert forall|i: int| 0 <= i <= str.len() implies is_prefix_pred(sub, str.subrange(i, str.len() as int)) || is_not_prefix_pred(sub, str.subrange(i, str.len() as int)) by {
        is_prefix_implies_or_not(sub, str.subrange(i, str.len() as int));
    };
}

proof fn not_prefix_implies_not_substring(sub: Seq<char>, str: Seq<char>)
    ensures
        is_not_substring_pred(sub, str) ==> !is_substring_pred(sub, str),
{
}

proof fn substring_implies_not_not_substring(sub: Seq<char>, str: Seq<char>)
    ensures
        is_substring_pred(sub, str) ==> !is_not_substring_pred(sub, str),
{
}

proof fn str_len_as_nat_to_int(str: Seq<char>) 
    ensures
        str.len() as int >= 0,
{
}

proof fn sub_len_as_nat_to_int(sub: Seq<char>) 
    ensures
        sub.len() as int >= 0,
{
}

spec fn str_subrange_len(str: Seq<char>, i: int, j: int) -> int
    recommends 0 <= i <= j <= str.len()
{
    j - i
}
// </vc-helpers>

// <vc-spec>
fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_substring_pred(sub, str),
        res ==> is_substring_pred(sub, str),
        // ensures  !res ==> !is_substring_pred(sub, str)
        is_substring_pred(sub, str) ==> res,
        is_substring_pred(sub, str) ==> res,
        !res <==> is_not_substring_pred(sub, str), // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    if sub.len() == 0 {
        proof {
            assert(is_substring_pred(sub, str)) by {
                assert(is_prefix_pred(sub, str.subrange(0, str.len() as int)));
            }
        }
        return true;
    }
    
    let str_len: usize = str.len();
    let sub_len: usize = sub.len();
    let str_len_int: int = str_len as int;
    let sub_len_int: int = sub_len as int;
    let mut i: usize = 0;
    
    while i <= str_len - sub_len
        invariant
            0 <= i <= str_len,
            forall|j: int| 0 <= j < i as int ==> is_not_prefix_pred(sub, str.subrange(j, str_len_int)),
    {
        let mut match_found = true;
        let mut k: usize = 0;
        
        while k < sub_len
            invariant
                0 <= k <= sub_len,
                match_found ==> forall|l: int| 0 <= l < k as int ==> sub[l] == str[i + l],
                !match_found ==> is_not_prefix_pred(sub, str.subrange(i as int, str_len_int)),
        {
            if i + k >= str_len || sub[k] != str[i + k] {
                match_found = false;
                break;
            }
            k = k + 1;
        }
        
        if match_found {
            proof {
                assert(is_prefix_pred(sub, str.subrange(i as int, str_len_int)));
                assert(is_substring_pred(sub, str));
            }
            return true;
        }
        
        proof {
            assert(is_not_prefix_pred(sub, str.subrange(i as int, str_len_int)));
        }
        i = i + 1;
    }
    
    proof {
        assert forall|j: int| 0 <= j <= str_len_int implies is_not_prefix_pred(sub, str.subrange(j, str_len_int)) by {
            if j < i as int {
                assert(0 <= j < i as int);
            } else {
                proof {
                    str_len_as_nat_to_int(str);
                    sub_len_as_nat_to_int(sub);
                }
                if j <= str_len_int - sub_len_int {
                    assert(j >= i as int);
                } else {
                    assert(sub_len_int > str_subrange_len(str, j, str_len_int));
                }
            }
        };
        assert(is_not_substring_pred(sub, str));
        is_substring_implies_or_not(sub, str);
        not_prefix_implies_not_substring(sub, str);
    }
    
    false
}
// </vc-code>

fn main() {}

}