use vstd::prelude::*;

verus! {

spec fn spec_sum(s: Seq<nat>) -> (ret: int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end
// pure-end

spec fn total_str_len(strings: Seq<&str>) -> (ret: int) {
    spec_sum(strings.map_values(|s: &str| s@.len()))
}
// pure-end
spec fn inner_expr_total_match<'a>(lst1: Vec<&'a str>, lst2: Vec<&'a str>, ret: Option<Vec<&'a str>>) -> (ret:bool) {
    ret.is_some() ==> ret.unwrap() == if total_str_len(lst1@) <= total_str_len(lst2@) {
        lst1
    } else {
        lst2
    }
}
// pure-end

// <vc-helpers>
spec fn spec_vec_sum_lengths(s: Seq<&str>) -> (ret: int) {
    s.fold_left(0, |x: int, y| x + y@.len())
}
// </vc-helpers>

// <vc-spec>
fn total_match<'a>(lst1: Vec<&'a str>, lst2: Vec<&'a str>) -> (ret: Option<Vec<&'a str>>)
    // post-conditions-start
    ensures
        ret.is_some() <== total_str_len(lst1@) <= usize::MAX && total_str_len(lst2@) <= usize::MAX,
        inner_expr_total_match(lst1, lst2, ret),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let sum1: int = 0;
    let sum2: int = 0;

    // Calculate total length of strings in lst1
    #[allow(unused_assignments)] // to avoid warning for an initialized variable not being mutated
    let mut current_sum1: int = 0;
    let mut i = 0;
    while i < lst1.len()
        invariant
            0 <= i <= lst1.len(),
            current_sum1 == spec_vec_sum_lengths(lst1.subsequence(0, i as int)),
            lst1.len() as int <= usize::MAX as int, // to ensure no overflow on conversion
    {
        current_sum1 = current_sum1 + lst1[i].len() as int;
        i = i + 1;
    }
    let total_len1 = current_sum1;
    proof {
        assert(total_len1 == total_str_len(lst1@));
    }

    // Calculate total length of strings in lst2
    #[allow(unused_assignments)] // to avoid warning for an initialized variable not being mutated
    let mut current_sum2: int = 0;
    let mut j = 0;
    while j < lst2.len()
        invariant
            0 <= j <= lst2.len(),
            current_sum2 == spec_vec_sum_lengths(lst2.subsequence(0, j as int)),
            lst2.len() as int <= usize::MAX as int, // to ensure no overflow on conversion
    {
        current_sum2 = current_sum2 + lst2[j].len() as int;
        j = j + 1;
    }
    let total_len2 = current_sum2;
    proof {
        assert(total_len2 == total_str_len(lst2@));
    }

    // Determine which list to return
    if total_len1 <= total_len2 {
        if total_len1 <= usize::MAX as int {
            Some(lst1)
        } else {
            None
        }
    } else {
        if total_len2 <= usize::MAX as int {
            Some(lst2)
        } else {
            None
        }
    }
    // impl-end
}
// </vc-code>

fn main() {}
}