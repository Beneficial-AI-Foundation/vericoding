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
fn is_prefix_impl(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res == is_prefix_predicate(pre, str),
{
    if pre.len() > str.len() {
        return false;
    }
    let mut i = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            pre.subrange(0, i) == str.subrange(0, i),
    {
        if pre[i] != str[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn is_substring_impl(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res == is_substring_predicate(sub, str)
{
    if sub.len() > str.len() {
        return false;
    }
    let mut i = 0;
    while i <= str.len() - sub.len()
        invariant
            0 <= i <= str.len() - sub.len() + 1,
            forall|ii: int| 0 <= ii < i ==> 
                !is_prefix_predicate(sub, str.subrange(ii, str.len() as int)),
    {
        if is_prefix_impl(sub, str.subrange(i, str.len())) {
            return true;
        }
        i += 1;
    }
    false
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

    let mut i = 0;
    while i <= str1.len() - k
        invariant
            0 <= i <= str1.len() - k + 1,
            forall|ii: int| 0 <= ii < i ==> 
                !is_substring_predicate(str1.subrange(ii, ii + k), str2),
    {
        let sub = str1.subrange(i, i + k);
        if is_substring_impl(sub, str2) {
            return true;
        }
        i += 1;
    }
    return false;
}
// </vc-code>

fn main() {}

}