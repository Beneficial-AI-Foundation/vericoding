// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prefix(prefix: Seq<char>, full: Seq<char>) -> bool {
    prefix.len() <= full.len() &&
    forall|k: int| 0 <= k < prefix.len() ==> prefix[k] == full[k]
}

spec fn exists_substring(str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|offset: int| 0 <= offset <= str1.len() - str2.len() &&
        is_prefix(str2, str1.subrange(offset, str1.len() as int))
}

spec fn post(str1: Seq<char>, str2: Seq<char>, found: bool, i: nat) -> bool {
    (found <==> exists_substring(str1, str2)) &&
    (found ==> i + str2.len() <= str1.len() && 
        is_prefix(str2, str1.subrange(i as int, str1.len() as int)))
}

spec fn outter_inv_correctness(str1: Seq<char>, str2: Seq<char>, found: bool, i: nat) -> bool {
    (found ==> (i + str2.len() <= str1.len() && 
        is_prefix(str2, str1.subrange(i as int, str1.len() as int)))) &&
    (!found && 0 < i <= str1.len() && i != str2.len() - 1 ==> 
        !(exists_substring(str1.subrange(0, i as int), str2))) &&
    (!found ==> i <= str1.len())
}

spec fn inner_inv_correctness(str1: Seq<char>, str2: Seq<char>, i: nat, j: int, found: bool) -> bool {
    0 <= j <= i &&
    j < str2.len() &&
    i < str1.len() &&
    (str1[i as int] == str2[j] ==> 
        is_prefix(str2.subrange(j, str2.len() as int), str1.subrange(i as int, str1.len() as int))) &&
    (found ==> j == 0 && str1[i as int] == str2[j])
}

spec fn inner_inv_termination(str1: Seq<char>, str2: Seq<char>, i: nat, j: int, old_i: nat, old_j: nat) -> bool {
    old_j - j == old_i - old_i
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(str1: Seq<char>, str2: Seq<char>) -> (result: (bool, usize))
    ensures post(str1, str2, result.0, result.1 as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}