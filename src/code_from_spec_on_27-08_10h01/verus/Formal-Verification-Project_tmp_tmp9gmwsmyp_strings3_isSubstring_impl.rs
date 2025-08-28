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
    false
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
proof fn lemma_is_not_substring_equiv(sub: Seq<char>, str: Seq<char>)
    ensures is_substring_pred(sub, str) <==> !is_not_substring_pred(sub, str)
{
}

proof fn lemma_prefix_subrange_valid(sub: Seq<char>, str: Seq<char>, i: int)
    requires 0 <= i <= str.len()
    ensures str.subrange(i, str.len() as int).len() == str.len() - i
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> is_substring_pred(sub, str)
    //ensures !res <==> is_not_substring_pred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if sub.len() == 0nat {
        return true;
    }
    
    if sub.len() > str.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= ((str.len() - sub.len()) as usize)
        invariant 
            0 <= i <= str.len() - sub.len() + 1,
            forall|j: int| 0 <= j < i ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int))
    {
        let ghost suffix_start: int = i as int;
        let ghost suffix_end: int = str.len() as int;
        let suffix = str.subrange(suffix_start, suffix_end);
        if is_prefix(sub, suffix) {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>

fn main() {}

}