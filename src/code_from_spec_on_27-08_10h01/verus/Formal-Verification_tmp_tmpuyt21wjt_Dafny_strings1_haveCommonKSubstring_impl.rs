use vstd::prelude::*;

verus! {

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}


fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_predicate(pre, str),
{
  assume(false);
  false
}



spec fn is_prefix_predicate(pre: Seq<char>, str: Seq<char>) -> bool {
  str.len() >= pre.len() && pre == str.subrange(0, pre.len() as int)
}


spec fn is_substring_predicate(sub: Seq<char>, str: Seq<char>) -> bool {
  str.len() >= sub.len() && 
  exists|i: int| 0 <= i <= str.len() && #[trigger] is_prefix_predicate(sub, str.subrange(i, str.len() as int))
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res == is_substring_predicate(sub, str)
{
  assume(false);
  false
}

spec fn have_common_k_substring_predicate(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
  str1.len() >= k && str2.len() >= k && 
  exists|i: int| 0 <= i <= str1.len() - k && 
      #[trigger] is_substring_predicate(
          str1.subrange(i, str1.len() as int).subrange(0, k as int), 
          str2
      )
}

spec fn max_common_substring_predicate(str1: Seq<char>, str2: Seq<char>, len: nat) -> bool {
   forall|k: int| len < k <= str1.len() ==> !#[trigger] have_common_k_substring_predicate(k as nat, str1, str2)
}

// <vc-helpers>
proof fn lemma_subrange_properties(s: Seq<char>, i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures s.subrange(i, j).len() == j - i
{
}

proof fn lemma_is_prefix_equiv(pre: Seq<char>, str: Seq<char>)
    ensures is_prefix_predicate(pre, str) == !is_not_prefix_pred(pre, str)
{
    if is_prefix_predicate(pre, str) {
        assert(str.len() >= pre.len());
        assert(pre == str.subrange(0, pre.len() as int));
        assert(!(pre.len() > str.len()));
        assert(!(pre != str.subrange(0, pre.len() as int)));
        assert(!is_not_prefix_pred(pre, str));
    }
    if !is_not_prefix_pred(pre, str) {
        assert(!(pre.len() > str.len()));
        assert(!(pre != str.subrange(0, pre.len() as int)));
        assert(str.len() >= pre.len());
        assert(pre == str.subrange(0, pre.len() as int));
        assert(is_prefix_predicate(pre, str));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn have_common_k_substring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures 
        (str1.len() < k || str2.len() < k) ==> !found,
        have_common_k_substring_predicate(k, str1, str2) == found,
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if str1.len() < k || str2.len() < k {
        return false;
    }
    
    let mut i: nat = 0;
    while i <= str1.len() - k
        invariant 
            0 <= i <= str1.len() - k + 1,
            str1.len() >= k,
            str2.len() >= k,
            forall|j: int| 0 <= j < i ==> !is_substring_predicate(
                str1.subrange(j, str1.len() as int).subrange(0, k as int),
                str2
            )
    {
        let ghost substr = str1.subrange(i as int, str1.len() as int).subrange(0, k as int);
        let is_sub = is_substring(substr, str2);
        
        if is_sub {
            assert(is_substring_predicate(substr, str2));
            assert(have_common_k_substring_predicate(k, str1, str2));
            return true;
        }
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j <= str1.len() - k ==> !is_substring_predicate(
        str1.subrange(j, str1.len() as int).subrange(0, k as int),
        str2
    ));
    assert(!have_common_k_substring_predicate(k, str1, str2));
    false
}
// </vc-code>

fn main() {}

}