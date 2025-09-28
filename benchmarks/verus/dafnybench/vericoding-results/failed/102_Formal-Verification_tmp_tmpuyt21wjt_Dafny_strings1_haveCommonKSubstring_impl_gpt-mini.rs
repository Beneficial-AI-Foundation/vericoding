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
spec fn match_at(k: nat, s1: Seq<char>, s2: Seq<char>, i: int, j: int) -> bool {
    forall|t: int| 0 <= t && t < k as int ==> s1@[i + t] == s2@[j + t]
}

proof fn seq_eq_from_elem_eq(s1: Seq<char>, s2: Seq<char>)
    requires s1.len() == s2.len();
    requires (forall|t: int| 0 <= t && t < s1.len() ==> s1@[t] == s2@[t]);
    ensures s1 == s2
{
    // Sequence extensionality: same length and same elements => equal
    assert((forall|t: int| 0 <= t && t < s1.len() ==> s1@[t] == s2@[t]));
    assert(s1 == s2);
}

proof fn subrange_indexing(s: Seq<char>, a: int, b: int, t: int)
    requires 0 <= a && a <= b && b <= s.len();
    requires 0 <= t && t < b - a;
    ensures s.subrange(a, b)@[t] == s@[a + t]
{
    assert(s.subrange(a, b)@[t] == s@[a + t]);
}

proof fn match_at_implies_prefix(k: nat, s1: Seq<char>, s2: Seq<char>, i: int, j: int)
    requires 0 <= i && i + k as int <= s1.len();
    requires 0 <= j && j + k as int <= s2.len();
    requires match_at(k, s1, s2, i, j);
    ensures is_prefix_predicate(s1.subrange(i, i + k as int), s2.subrange(j, s2.len()))
{
    let k_i = k as int;
    // From match_at we know element-wise equality for t in 0..k-1
    assert((forall|t: int| 0 <= t && t < k_i ==> s1@[i + t] == s2@[j + t]));

    // Translate to equality of the k-length subranges element-wise.
    assert((forall|t: int| 0 <= t && t < k_i ==>
        { subrange_indexing(s1, i, i + k_i, t); subrange_indexing(s2, j, j + k_i, t); }
        s1.subrange(i, i + k_i)@[t] == s2.subrange(j, j + k_i)@[t]
    ));

    // The two k-length subranges are equal.
    seq_eq_from_elem_eq(s1.subrange(i, i + k_i), s2.subrange(j, j + k_i));

    // Now the prefix relationship holds: the target suffix has length >= k and its first k chars equal the pre.
    assert(s2.subrange(j, s2.len()).len() >= s1.subrange(i, i + k_i).len());
    assert(is_prefix_predicate(s1.subrange(i, i + k_i), s2.subrange(j, s2.len())));
}

proof fn prefix_implies_match_at(k: nat, s1: Seq<char>, s2: Seq<char>, i: int, j: int)
    requires 0 <= i && i + k as int <= s1.len();
    requires 0 <= j && j + k as int <= s2.len();
    requires is_prefix_predicate(s1.subrange(i, i + k as int), s2.subrange(j, s2.len()));
    ensures match_at(k, s1, s2, i, j)
{
    let k_i = k as int;
    // From prefix predicate, the k-length pre equals the first k of the suffix.
    // So for each t < k, s1@[i+t] == s1.subrange(i,i+k)@[t] == s2.subrange(j,j+k)@[t] == s2@[j+t]
    assert((forall|t: int| 0 <= t && t < k_i ==>
        { subrange_indexing(s1, i, i + k_i, t); subrange_indexing(s2, j, j + k_i, t); }
        s1@[i + t] == s2@[j + t]
    ));
    // Thus match_at holds.
    assert((forall|t: int| 0 <= t && t < k_i ==> s1@[i + t] == s2@[j + t]));
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
    // If either string is too short, there cannot be a common substring of length k.
    let k_int = k as int;
    if str1.len() < k_int || str2.len() < k_int {
        proof {
            // By definition, have_common_k_substring_predicate requires both lengths >= k.
            assert(!(str1.len() >= k_int && str2.len() >= k_int));
            assert(!have_common_k_substring_predicate(k, str1, str2));
        }
        return false;
    }

    let max_i: int = str1.len() - k_int;
    let max_j: int = str2.len() - k_int;

    let mut i: int = 0;
    while i <= max_i
        invariant 0 <= i && i <= max_i + 1
        invariant (forall|ii: int| 0 <= ii && ii < i ==>
            ! (exists|jj: int| 0 <= jj && jj <= max_j && #[trigger] match_at(k, str1, str2, ii, jj)))
    {
        let mut j: int = 0;
        while j <= max_j
            invariant 0 <= j && j <= max_j + 1
            invariant (forall|jj: int| 0 <= jj && jj < j ==> ! (#[trigger] match_at(k, str1, str2, i, jj)))
        {
            // Check element-wise equality of length k starting at (i,j)
            let mut t: int = 0;
            let mut all_eq: bool = true;
            while t < k_int
                invariant 0 <= t && t <= k_int
                invariant all_eq ==> (forall|u: int| 0 <= u && u < t ==> str1@[i + u] == str2@[j + u])
            {
                if str1@[i + t] != str2@[j + t] {
                    all_eq = false;
                } else {
                    all_eq = all_eq;
                }
                t = t + 1;
            }

            if all_eq {
                // We found indices i, j such that for all t in 0..k-1 str1[i+t] == str2[j+t].
                // Prove the specification predicate holds, then return true.
                proof {
                    let i0 = i;
                    let j0 = j;
                    let k_i = k as int;

                    // From the inner loop invariant and termination we have element-wise equality:
                    assert((forall|u: int| 0 <= u && u < k_i ==> str1@[i0 + u] == str2@[j0 + u]));

                    // Using subrange_indexing, translate to equality of the k-length subranges.
                    assert((forall|u: int| 0 <= u && u < k_i ==>
                        { subrange_indexing(str1, i0, i0 + k_i, u); subrange_indexing(str2, j0, j0 + k_i, u); }
                        str1.subrange(i0, i0 + k_i)@[u] == str2.subrange(j0, j0 + k_i)@[u]
                    ));

                    // The two k-length subranges are equal.
                    seq_eq_from_elem_eq(str1.subrange(i0, i0 + k_i), str2.subrange(j0, j0 + k_i));

                    // From equality of k-length subranges, prefix relation holds for the appropriate suffix.
                    match_at_implies_prefix(k, str1, str2, i0, j0);

                    // Hence str1.subrange(i0, i0+k) is a substring of str2 (witness j0).
                    assert(is_substring_predicate(str1.subrange(i0, i0 + k_i), str2));

                    // And since i0 is in the valid range 0..=max_i, the top-level predicate holds.
                    assert(0 <= i0 && i0 <= max_i);
                    assert(have_common_k_substring_predicate(k, str1, str2));
                }
                return true;
            }

            j = j + 1;
        }

        i = i + 1;
    }

    // If we reach here, no matching substring was found.
    proof {
        // From the outer loop invariant and exit condition, for all valid starting positions ii,
        // there does not exist jj such that the substrings match element-wise.
        // i must be max_i + 1 on loop exit.
        assert(i == max_i + 1);
        assert((forall|ii: int| 0 <= ii && ii < i ==>
            ! (exists|jj: int| 0 <= jj && jj <= max_j && #[trigger] match_at(k, str1, str2, ii, jj))));

        // Therefore for all ii in 0..=max_i there is no jj where match_at holds.
        assert((forall|ii: int| 0 <= ii && ii <= max_i ==>
            ! (exists|jj: int| 0 <= jj && jj <= max_j && #[trigger] match_at(k, str1, str2, ii, jj))));

        // Now show that this implies the have_common_k_substring_predicate is false.
        // Suppose for contradiction that there exists ii in 0..=max_i with is_substring_predicate(str1.subrange(ii, ii+k), str2).
        // Then there exists jj with is_prefix_predicate(str1.subrange(ii, ii+k), str2.subrange(jj, str2.len())).
        // From the prefix relation we can derive match_at, contradicting the invariant above.
        assert(!(exists|ii: int| 0 <= ii && ii <= max_i && #[trigger] is_substring_predicate(str1.subrange(ii, ii + k_int), str2)));
        // Therefore the existential in have_common_k_substring_predicate is false, so the predicate is false.
        assert(!have_common_k_substring_predicate(k, str1, str2));
    }

    return false;
}
// </vc-code>

fn main() {}

}