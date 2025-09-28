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
spec fn is_prefix_predicate(pre: Seq<char>, str: Seq<char>) -> bool {
  str.len() >= pre.len() && pre == str.subrange(0, pre.len() as int)
}

proof fn is_prefix_predicate_implies_not_is_not_prefix_pred(pre: Seq<char>, str: Seq<char>)
    ensures
        is_prefix_predicate(pre, str) ==> !is_not_prefix_pred(pre, str)
{
}

proof fn not_is_not_prefix_pred_implies_is_prefix_predicate(pre: Seq<char>, str: Seq<char>)
    ensures
        !is_not_prefix_pred(pre, str) ==> is_prefix_predicate(pre, str)
{
}

fn is_prefix_impl(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_predicate(pre, str),
{
    if pre.len() > str.len() {
        false
    } else {
        let mut i: usize = 0;
        while i < pre.len()
            invariant
                0 <= i <= pre.len(),
                forall|j: int| 0 <= j < i ==> pre@[j] == str@[j],
        {
            if pre@[i] != str@[i] {
                return false;
            }
            i = i + 1;
        }
        true
    }
}

fn is_substring_impl(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res == is_substring_predicate(sub, str)
{
    if sub.len() > str.len() {
        false
    } else {
        let mut i: usize = 0;
        let max_i = str.len() - sub.len();
        while i <= max_i
            invariant
                0 <= i <= max_i + 1,
                forall|j: int| 0 <= j < i ==> !is_prefix_predicate(sub, str.subrange(j, str.len() as int)),
        {
            let remaining = str.subrange(i, str.len());
            if is_prefix_impl(sub, remaining) {
                return true;
            }
            i = i + 1;
        }
        false
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
    if k > str1.len() || k > str2.len() {
        false
    } else {
        let mut i: usize = 0;
        let max_i = str1.len() - k;
        while i <= max_i
            invariant
                0 <= i <= max_i + 1,
                forall|j: int| 0 <= j < i ==> !is_substring_predicate(str1.subrange(j, j + k), str2),
        {
            let substr = str1.subrange(i, i + k);
            if is_substring_impl(substr, str2) {
                return true;
            }
            i = i + 1;
        }
        false
    }
}
// </vc-code>

fn main() {}

}