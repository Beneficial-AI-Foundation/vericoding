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
fn sum_lengths(vec: &Vec<&str>) -> (ret: (usize, bool, int)) {
    let mut sum: usize = 0;
    let mut overflow: bool = false;
    let tracked mut ghost_sum: int = 0;

    for j in 0..vec.len()
        invariant
            ghost_sum == total_str_len(vec@.take(j)),
            !overflow ==> (sum as int == ghost_sum),
    {
        proof {
            let len = vec[j].len();
            assert(len as int == vec@[j]@.len());
            ghost_sum = ghost_sum + vec@[j]@.len();
        };

        let len = vec[j].len();

        let new_sum = sum.checked_add(len);
        if new_sum.is_none() {
            overflow = true;
            sum = usize::MAX;
        } else {
            sum = new_sum.unwrap();
        }
    }

    (sum, overflow, ghost_sum)
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
    let (total1, overflow1, ghost_total1) = sum_lengths(&lst1);
    let (total2, overflow2, ghost_total2) = sum_lengths(&lst2);

    if overflow1 || overflow2 {
        return None;
    } else {
        proof {
            assert(ghost_total1 == total1 as int);
            assert(ghost_total2 == total2 as int);
            assert(total_str_len(lst1@) == ghost_total1);
            assert(total_str_len(lst2@) == ghost_total2);
            if (total1 as int) <= (total2 as int) {
                assert(total_str_len(lst1@) <= total_str_len(lst2@));
            } else {
                assert(total_str_len(lst1@) > total_str_len(lst2@));
            }
        };

        if total1 <= total2 {
            return Some(lst1);
        } else {
            return Some(lst2);
        }
    }
}
// </vc-code>

fn main() {}
}