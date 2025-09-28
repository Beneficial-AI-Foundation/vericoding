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
// No additional helpers needed
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
            forall|j: int| 0 <= j < i ==> !#[trigger] is_substring_predicate(
                str1.subrange(j, str1.len() as int).subrange(0, k as int),
                str2
            ),
    {
        let sub = proof {
            let i_int: int = i as int;
            let k_int: int = k as int;
            let str1_len_int: int = str1.len() as int;
            
            let sub = str1.subrange(i_int, str1_len_int).subrange(0, k_int);
            assert(sub == str1.subrange(i_int, i_int + k_int));
            sub
        };
        
        if is_substring(sub, str2) {
            proof {
                assert(is_substring_predicate(sub, str2));
                assert(have_common_k_substring_predicate(k, str1, str2));
            }
            return true;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == str1.len() - k + 1);
        assert(forall|j: int| 0 <= j <= str1.len() - k ==> !#[trigger] is_substring_predicate(
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