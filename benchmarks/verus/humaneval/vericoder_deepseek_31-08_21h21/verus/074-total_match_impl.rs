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
proof fn lemma_vec_len_bound<T>(v: &Vec<T>)
    ensures
        v@.len() <= usize::MAX as int,
{
}

proof fn lemma_total_str_len_bound(strings: &Vec<&str>)
    ensures
        total_str_len(strings@) <= usize::MAX,
    decreases strings@.len(),
{
    lemma_vec_len_bound(strings);
    if strings@.len() > 0 {
        let sub_vec = Vec::from_slice(&strings[1..]);
        lemma_total_str_len_bound(&sub_vec);
        assert(sub_vec@ == strings@.subrange(1, strings@.len() as int));
    }
}

proof fn lemma_spec_sum_ge_zero(s: Seq<nat>) 
    ensures
        spec_sum(s) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_spec_sum_ge_zero(s.subrange(1, s.len() as int));
    }
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
    let mut total1: usize = 0;
    let mut total2: usize = 0;
    let mut i: usize = 0;
    proof {
        lemma_total_str_len_bound(&lst1);
        lemma_total_str_len_bound(&lst2);
    }
    while i < lst1.len() 
        invariant 
            i <= lst1.len(),
            total1 as int == spec_sum(lst1@.subrange(0, i as int).map_values(|s: &str| s@.len())),
            total1 as int <= usize::MAX,
        decreases lst1.len() - i,
    {
        let s = lst1[i];
        total1 = total1 + s.len();
        i = i + 1;
    }
    
    i = 0;
    while i < lst2.len() 
        invariant 
            i <= lst2.len(),
            total2 as int == spec_sum(lst2@.subrange(0, i as int).map_values(|s: &str| s@.len())),
            total2 as int <= usize::MAX,
        decreases lst2.len() - i,
    {
        let s = lst2[i];
        total2 = total2 + s.len();
        i = i + 1;
    }
    
    proof {
        assert(total_str_len(lst1@) == spec_sum(lst1@.map_values(|s: &str| s@.len())));
        assert(total_str_len(lst2@) == spec_sum(lst2@.map_values(|s: &str| s@.len())));
        assert(total1 as int == total_str_len(lst1@));
        assert(total2 as int == total_str_len(lst2@));
    }
    
    if total1 <= total2 {
        Some(lst1)
    } else {
        Some(lst2)
    }
}
// </vc-code>

fn main() {}
}