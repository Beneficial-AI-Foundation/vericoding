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
proof fn str_len_eq(s: &str) {
    // The runtime length of a string equals its specification-level length.
    assert((s.len() as int) == (s@.len() as int));
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
    let mut i1: usize = 0;
    let mut sum1: usize = 0;
    let mut overflow1: bool = false;
    while i1 < lst1.len() {
        invariant 0 <= i1 && i1 <= lst1.len();
        // We don't assert relations involving `int` here; we only maintain bounds on indices.
        let l = lst1[i1].len();
        match sum1.checked_add(l) {
            Some(ns) => {
                sum1 = ns;
                i1 = i1 + 1;
            }
            None => {
                overflow1 = true;
                break;
            }
        }
    }

    let mut i2: usize = 0;
    let mut sum2: usize = 0;
    let mut overflow2: bool = false;
    while i2 < lst2.len() {
        invariant 0 <= i2 && i2 <= lst2.len();
        let l = lst2[i2].len();
        match sum2.checked_add(l) {
            Some(ns) => {
                sum2 = ns;
                i2 = i2 + 1;
            }
            None => {
                overflow2 = true;
                break;
            }
        }
    }

    let ret = if overflow1 || overflow2 {
        None
    } else {
        if sum1 <= sum2 {
            Some(lst1)
        } else {
            Some(lst2)
        }
    };

    proof {
        // If we returned Some, then both lists did not overflow and we can relate runtime sums
        // to the specification total_str_len, and show the chosen list matches the spec comparison.
        if !overflow1 && !overflow2 {
            // Prove for lst1: runtime sum1 equals total_str_len(lst1@)
            {
                let mut j: usize = 0;
                let mut acc_runtime: int = 0;
                let mut acc_spec: int = 0;
                while j < lst1.len() {
                    invariant 0 <= j && j <= lst1.len();
                    invariant acc_runtime == acc_spec;
                    let s = lst1[j];
                    // accumulate runtime and spec lengths in parallel
                    acc_runtime = acc_runtime + (s.len() as int);
                    acc_spec = acc_spec + (s@.len() as int);
                    // relate the two lengths for this element
                    str_len_eq(s);
                    j = j + 1;
                }
                // acc_spec is total_str_len(lst1@)
                assert(acc_spec == total_str_len(lst1@));
                // acc_runtime equals sum1 as int
                assert(acc_runtime == (sum1 as int));
            }
            // Prove for lst2: runtime sum2 equals total_str_len(lst2@)
            {
                let mut j: usize = 0;
                let mut acc_runtime: int = 0;
                let mut acc_spec: int = 0;
                while j < lst2.len() {
                    invariant 0 <= j && j <= lst2.len();
                    invariant acc_runtime == acc_spec;
                    let s = lst2[j];
                    acc_runtime = acc_runtime + (s.len() as int);
                    acc_spec = acc_spec + (s@.len() as int);
                    str_len_eq(s);
                    j = j + 1;
                }
                assert(acc_spec == total_str_len(lst2@));
                assert(acc_runtime == (sum2 as int));
            }
            // Now relate the chosen list in `ret` to the specification comparison.
            if sum1 <= sum2 {
                // From above, sum1 as int == total_str_len(lst1@) and sum2 as int == total_str_len(lst2@)
                assert((sum1 as int) <= (sum2 as int));
                assert(total_str_len(lst1@) <= total_str_len(lst2@));
                assert(ret.is_some());
                assert(ret.unwrap() == lst1);
            } else {
                assert((sum2 as int) < (sum1 as int));
                assert(total_str_len(lst2@) < total_str_len(lst1@));
                assert(ret.is_some());
                assert(ret.unwrap() == lst2);
            }
        }
    }

    ret
}
// </vc-code>

fn main() {}
}