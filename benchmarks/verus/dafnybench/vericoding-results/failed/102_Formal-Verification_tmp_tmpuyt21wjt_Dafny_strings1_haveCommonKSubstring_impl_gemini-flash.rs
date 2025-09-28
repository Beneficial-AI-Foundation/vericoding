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
spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}


fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_predicate(pre, str),
{
    if pre.len() > str.len() {
        false
    } else {
        pre == str.subrange(0, pre.len() as int)
    }
}



spec fn is_prefix_predicate(pre: Seq<char>, str: Seq<char>) -> bool {
  str.len() >= pre.len() && pre == str.subrange(0, pre.len() as int)
}


spec fn is_substring_predicate(sub: Seq<char>, str: Seq<char>) -> bool {
  str.len() >= sub.len() && 
  exists|i: int| 0 <= i && (i as nat) <= str.len() - sub.len() && #[trigger] is_prefix_predicate(sub, str.subrange(i, str.len() as int))
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res == is_substring_predicate(sub, str)
{
    if sub.len() > str.len() {
        false
    } else {
        let mut i: nat = 0;
        let mut found: bool = false;

        while i <= str.len() - sub.len() && !found
            invariant
                0 <= i as int,
                i <= str.len() - sub.len() + 1,
                found == exists|j: int| 0 <= j && (j as nat) < i && is_prefix_predicate(sub, str.subrange(j, str.len() as int)),
                sub.len() <= str.len(),
            decreases (str.len() - sub.len() - i) as int
        {
            if is_prefix(sub, str.subrange(i, str.len() as int)) {
                found = true;
            }
            i = i + 1;
        }
        found
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

    let k_nat = k;
    let mut i: nat = 0;
    let mut found: bool = false;

    while i <= str1.len() - k_nat && !found
        invariant
            0 <= i as int,
            i <= str1.len() - k_nat + 1,
            found == exists|j: int| 0 <= j && (j as nat) < i && is_substring_predicate(str1.subrange(j, (j + k_nat) as int), str2),
            k_nat <= str1.len(),
            k_nat <= str2.len(),
        decreases (str1.len() - k_nat - i) as int
    {
        let sub_k = str1.subrange(i, (i + k_nat) as int);
        if is_substring(sub_k, str2) {
            found = true;
        }
        i = i + 1;
    }
    found
}
// </vc-code>

fn main() {}

}