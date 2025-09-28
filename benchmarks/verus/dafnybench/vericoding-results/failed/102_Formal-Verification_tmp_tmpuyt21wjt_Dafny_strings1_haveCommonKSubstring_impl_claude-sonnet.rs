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
proof fn lemma_subrange_length(s: Seq<char>, start: int, end: int)
    requires 0 <= start <= end <= s.len()
    ensures s.subrange(start, end).len() == end - start
{}

proof fn lemma_is_prefix_correct(pre: Seq<char>, str: Seq<char>)
    ensures is_prefix_predicate(pre, str) == !is_not_prefix_pred(pre, str)
{
    if is_prefix_predicate(pre, str) {
        assert(str.len() >= pre.len());
        assert(pre == str.subrange(0, pre.len() as int));
        assert(!(pre.len() > str.len()));
        assert(!(pre != str.subrange(0, pre.len() as int)));
        assert(!is_not_prefix_pred(pre, str));
    } else {
        if pre.len() > str.len() {
            assert(is_not_prefix_pred(pre, str));
        } else {
            assert(str.len() >= pre.len());
            assert(pre != str.subrange(0, pre.len() as int));
            assert(is_not_prefix_pred(pre, str));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn have_common_k_substring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures 
        (str1.len() < k || str2.len() < k) ==> !found,
        have_common_k_substring_predicate(k, str1, str2) == found,
// </vc-spec>
// <vc-code>
{
    if str1.len() < k || str2.len() < k {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= str1.len() - k
        invariant
            0 <= i <= str1.len() - k + 1,
            str1.len() >= k,
            str2.len() >= k,
            forall|j: int| 0 <= j < i ==> !is_substring_predicate(
                str1.subrange(j, str1.len() as int).subrange(0, k as int), 
                str2
            )
        ensures
            i > str1.len() - k ==> 
                forall|j: int| 0 <= j <= str1.len() - k ==> !is_substring_predicate(
                    str1.subrange(j, str1.len() as int).subrange(0, k as int), 
                    str2
                )
    {
        let substring = str1.subrange(i as int, str1.len() as int).subrange(0, k as int);
        
        proof {
            lemma_subrange_length(str1.subrange(i as int, str1.len() as int), 0, k as int);
            assert(str1.subrange(i as int, str1.len() as int).len() >= k);
        }
        
        let found = is_substring(substring, str2);
        
        if found {
            proof {
                assert(is_substring_predicate(substring, str2));
                assert(exists|j: int| 0 <= j <= str1.len() - k && 
                    #[trigger] is_substring_predicate(
                        str1.subrange(j, str1.len() as int).subrange(0, k as int), 
                        str2
                    )) by {
                    assert(is_substring_predicate(
                        str1.subrange(i as int, str1.len() as int).subrange(0, k as int), 
                        str2
                    ));
                }
            }
            return true;
        }
        
        i += 1;
    }
    
    proof {
        assert(forall|j: int| 0 <= j <= str1.len() - k ==> !is_substring_predicate(
            str1.subrange(j, str1.len() as int).subrange(0, k as int), 
            str2
        ));
        assert(!have_common_k_substring_predicate(k, str1, str2));
    }
    
    false
}
// </vc-code>

fn main() {}

}