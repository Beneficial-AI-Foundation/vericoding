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
// <vc-helpers>
// </vc-helpers>
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
    let mut total1: usize = 0;
    let mut overflow1: bool = false;
    let tracked mut gtotal1: int = 0;
    for i in 0..lst1.len()
        invariant
            0 <= i <= lst1.len(),
            gtotal1 == spec_sum(lst1@.subrange(0, i as int).map_values(|s: &str| s@.len())),
            !overflow1 ==> total1 as int == gtotal1,
            !overflow1 ==> total1 <= usize::MAX,
            overflow1 ==> total1 as int < gtotal1,
    {
        let len = lst1[i].len();
        if !overflow1 {
            if let Some(new) = total1.checked_add(len) {
                total1 = new;
            } else {
                overflow1 = true;
            }
        }
        proof {
            gtotal1 = gtotal1 + (len as int);
        }
    }
    assert(gtotal1 == spec_sum(lst1@.map_values(|s: &str| s@.len())));
    assert(total_str_len(lst1@) == gtotal1);
    assert(!overflow1 ==> total_str_len(lst1@) <= usize::MAX);
    assert(overflow1 || total1 as int == gtotal1);

    let mut total2: usize = 0;
    let mut overflow2: bool = false;
    let tracked mut gtotal2: int = 0;
    for i in 0..lst2.len()
        invariant
            0 <= i <= lst2.len(),
            gtotal2 == spec_sum(lst2@.subrange(0, i as int).map_values(|s: &str| s@.len())),
            !overflow2 ==> total2 as int == gtotal2,
            !overflow2 ==> total2 <= usize::MAX,
            overflow2 ==> total2 as int < gtotal2,
    {
        let len = lst2[i].len();
        if !overflow2 {
            if let Some(new) = total2.checked_add(len) {
                total2 = new;
            } else {
                overflow2 = true;
            }
        }
        proof {
            gtotal2 = gtotal2 + (len as int);
        }
    }
    assert(gtotal2 == spec_sum(lst2@.map_values(|s: &str| s@.len())));
    assert(total_str_len(lst2@) == gtotal2);
    assert(!overflow2 ==> total_str_len(lst2@) <= usize::MAX);
    assert(overflow2 || total2 as int == gtotal2);

    if !overflow1 && !overflow2 {
        if total1 <= total2 {
            assert(total_str_len(lst1@) <= total_str_len(lst2@));
            Some(lst1)
        } else {
            assert(total_str_len(lst1@) > total_str_len(lst2@));
            Some(lst2)
        }
    } else {
        None
    }
}
// </vc-code>

fn main() {}
}