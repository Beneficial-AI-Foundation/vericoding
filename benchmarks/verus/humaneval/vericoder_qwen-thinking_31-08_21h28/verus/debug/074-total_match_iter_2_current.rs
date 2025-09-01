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
    let mut sum1 = 0;
    let mut overflow1 = false;
    for s in lst1 {
        invariant (overflow1 || sum1 <= usize::MAX);
        let len = s.len();
        if sum1 > usize::MAX - len {
            overflow1 = true;
            break;
        }
        sum1 += len;
    }
    if overflow1 {
        None
    } else {
        let mut sum2 = 0;
        let mut overflow2 = false;
        for s in lst2 {
            invariant (overflow2 || sum2 <= usize::MAX);
            let len = s.len();
            if sum2 > usize::MAX - len {
                overflow2 = true;
                break;
            }
            sum2 += len;
        }
        if overflow2 {
            None
        } else {
            if sum1 <= sum2 {
                Some(lst1)
            } else {
                Some(lst2)
            }
        }
    }
}
// </vc-code>

fn main() {}
}