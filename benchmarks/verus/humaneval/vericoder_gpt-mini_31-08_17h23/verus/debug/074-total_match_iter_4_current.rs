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
// No helpers needed for this verification
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
    let mut s1: int = 0;
    let mut i: usize = 0;
    while i < lst1.len()
        invariant {
            i <= lst1.len()
            s1 == total_str_len(lst1@.slice(0, i))
        }
    {
        let st: &str = lst1[i];
        s1 = s1 + (st.len() as int);
        i += 1;
    }

    let mut s2: int = 0;
    let mut j: usize = 0;
    while j < lst2.len()
        invariant {
            j <= lst2.len()
            s2 == total_str_len(lst2@.slice(0, j))
        }
    {
        let st: &str = lst2[j];
        s2 = s2 + (st.len() as int);
        j += 1;
    }

    // Now s1 == total_str_len(lst1@) and s2 == total_str_len(lst2@)
    let max_i: int = usize::MAX as int;
    if s1 <= s2 {
        if s1 <= max_i && s2 <= max_i {
            proof {
                assert(s1 == total_str_len(lst1@));
                assert(s2 == total_str_len(lst2@));
            }
            Some(lst1)
        } else {
            None
        }
    } else {
        if s1 <= max_i && s2 <= max_i {
            proof {
                assert(s1 == total_str_len(lst1@));
                assert(s2 == total_str_len(lst2@));
            }
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