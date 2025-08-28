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

proof fn prefix_implies_not_prefix(pre: Seq<char>, str: Seq<char>)
    ensures
        is_prefix_predicate(pre, str) ==> !is_not_prefix_pred(pre, str),
        !is_prefix_predicate(pre, str) ==> is_not_prefix_pred(pre, str),
{
    if is_prefix_predicate(pre, str) {
        assert(str.len() >= pre.len());
        assert(pre == str.subrange(0, pre.len() as int));
    } else {
        if pre.len() > str.len() {
            assert(is_not_prefix_pred(pre, str));
        } else {
            assert(pre != str.subrange(0, pre.len() as int));
            assert(is_not_prefix_pred(pre, str));
        }
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
fn have_common_k_substring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        (str1.len() < k || str2.len() < k) ==> !found,
        have_common_k_substring_predicate(k, str1, str2) == found,
{
    if str1.len() < k || str2.len() < k {
        return false;
    }

    let mut i: int = 0;
    while i <= str1.len() - k
        invariant
            0 <= i <= str1.len() - k + 1,
            forall|j: int| 0 <= j < i ==> !is_substring_predicate(
                str1.subrange(j, j + k as int),
                str2
            ),
        decreases str1.len() - k - i,
    {
        let substr = str1.subrange(i, i + k as int);
        let mut j: int = 0;
        let mut is_substr = false;

        while j <= str2.len() - k
            invariant
                0 <= j <= str2.len() - k + 1,
                !is_substr ==> forall|m: int| 0 <= m < j ==> !is_prefix_predicate(substr, str2.subrange(m, str2.len() as int)),
                is_substr ==> exists|m: int| 0 <= m < j && #[trigger] is_prefix_predicate(substr, str2.subrange(m, str2.len() as int)),
            decreases str2.len() - k - j,
        {
            let prefix_check = str2.subrange(j, str2.len() as int);
            if prefix_check.len() >= substr.len() && substr == prefix_check.subrange(0, substr.len() as int) {
                is_substr = true;
                break;
            }
            j = j + 1;
        }

        if is_substr {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {}

}