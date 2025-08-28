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
fn checked_total_str_len(lst: &Vec<&str>) -> (ret: Option<usize>)
    // post-conditions-start
    ensures
        ret.is_some() <==> total_str_len(lst@) <= usize::MAX,
        ret.is_some() <==> ret.unwrap() == total_str_len(lst@),
    // post-conditions-end
{
    // impl-start
    let ghost lens = Seq::<nat>::empty();
    let mut sum: usize = 0;
    for i in 0..lst.len()
        // invariants-start
        invariant
            sum == lst@.subrange(0, i as int).map_values(|s: &str| s@.len()).fold_left(
                0,
                |x: int, y| x + y,
            ),
            spec_sum(lens) == sum,
            lens =~= lst@.map_values(|s: &str| s@.len()).take(i as int),
            lens =~= lst@.take(i as int).map_values(|s: &str| s@.len()),
        // invariants-end
    {
        let x = lst[i].unicode_len();
        // assert-start
        proof {
            assert(lens.push(x as nat).drop_last() == lens);
            lens = lens.push(x as nat);
            assert(lens =~= lst@.map_values(|s: &str| s@.len()).take(i + 1));

            lemma_increasing_sum(lst@.map_values(|s: &str| s@.len()), i + 1, lst@.len() as int);
            assert(total_str_len(lst@) >= spec_sum(lens)) by {
                assert(lst@.map_values(|s: &str| s@.len()) =~= lst@.map_values(
                    |s: &str| s@.len(),
                ).take(lst@.len() as int));
            }
            if x + sum > usize::MAX {
                assert(sum.checked_add(x).is_none());
                assert(total_str_len(lst@) > usize::MAX);
            }
        }
        // assert-end
        sum = sum.checked_add(x)?;
        // assert-start
        assert(lst@.take(i + 1).map_values(|s: &str| s@.len()).drop_last() == lst@.take(
            i as int,
        ).map_values(|s: &str| s@.len()));
        // assert-end
    }
    assert(lst@ == lst@.subrange(0, lst.len() as int)); // assert-line
    return Some(sum);
    // impl-end
}

// pure-end

proof fn lemma_increasing_sum(s: Seq<nat>, i: int, j: int)
    // pre-conditions-start
    requires
        0 <= i <= j <= s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)),
    decreases j - i,
    // post-conditions-end
{
    // impl-start
    if (i < j) {
        assert(spec_sum(s.subrange(0, j - 1)) <= spec_sum(s.subrange(0, j))) by {
            assert(s.subrange(0, j).drop_last() == s.subrange(0, j - 1));
        }
        lemma_increasing_sum(s, i, j - 1);
    }
    // impl-end
}
// pure-end
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
    let len1 = checked_total_str_len(&lst1);
    let len2 = checked_total_str_len(&lst2);
    
    match (len1, len2) {
        (Some(l1), Some(l2)) => {
            if l1 <= l2 {
                Some(lst1)
            } else {
                Some(lst2)
            }
        }
        _ => None
    }
    // impl-end
}
// </vc-code>

}
fn main() {}