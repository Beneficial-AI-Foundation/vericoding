use vstd::prelude::*;

verus! {

spec fn spec_sum(s: Seq<nat>) -> (ret: int) {
    s.fold_left(0, |x: int, y| x + y)
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

spec fn total_str_len(strings: Seq<&str>) -> (ret: int) {
    spec_sum(strings.map_values(|s: &str| s@.len()))
}
// pure-end

fn checked_total_str_len(lst: &Vec<&str>) -> (ret: Option<usize>)
    // post-conditions-start
    ensures
        ret.is_some() <==> total_str_len(lst@) <= usize::MAX,
        ret.is_some() <==> ret.unwrap() == total_str_len(lst@),
    // post-conditions-end
{
    let mut total: usize = 0;
    let mut i = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            total == total_str_len(lst@.subrange(0, i as int)),
            total <= usize::MAX,
    {
        /* code modified by LLM (iteration 1): get string length as usize directly */
        let str_len = lst[i].len();
        
        /* code modified by LLM (iteration 1): check for overflow before addition */
        if total > usize::MAX - str_len {
            return None;
        }
        
        /* code modified by LLM (iteration 1): perform addition with usize values */
        total = total + str_len;
        i = i + 1;
    }
    
    Some(total)
}

spec fn inner_expr_total_match<'a>(lst1: Vec<&'a str>, lst2: Vec<&'a str>, ret: Option<Vec<&'a str>>) -> (ret:bool) {
    ret.is_some() ==> ret.unwrap() == if total_str_len(lst1@) <= total_str_len(lst2@) {
        lst1
    } else {
        lst2
    }
}
// pure-end

fn total_match<'a>(lst1: Vec<&'a str>, lst2: Vec<&'a str>) -> (ret: Option<Vec<&'a str>>)
    // post-conditions-start
    ensures
        ret.is_some() <== total_str_len(lst1@) <= usize::MAX && total_str_len(lst2@) <= usize::MAX,
        inner_expr_total_match(lst1, lst2, ret),
    // post-conditions-end
{
    let total1 = checked_total_str_len(&lst1);
    let total2 = checked_total_str_len(&lst2);
    
    match (total1, total2) {
        (Some(t1), Some(t2)) => {
            if t1 <= t2 {
                Some(lst1)
            } else {
                Some(lst2)
            }
        }
        _ => None
    }
}

}
fn main() {}