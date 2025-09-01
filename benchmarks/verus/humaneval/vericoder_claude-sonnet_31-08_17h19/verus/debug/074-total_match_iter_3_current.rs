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
proof fn lemma_spec_sum_nonneg(s: Seq<nat>)
    ensures spec_sum(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_spec_sum_nonneg(s.drop_last());
    }
}

proof fn lemma_total_str_len_nonneg(strings: Seq<&str>)
    ensures total_str_len(strings) >= 0
{
    lemma_spec_sum_nonneg(strings.map_values(|s: &str| s@.len()));
}

proof fn lemma_spec_sum_bounded(s: Seq<nat>, bound: nat)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] <= bound
    ensures spec_sum(s) <= s.len() * bound
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_spec_sum_bounded(s.drop_last(), bound);
    }
}

proof fn lemma_total_str_len_bounded(strings: Seq<&str>)
    requires forall|i: int| 0 <= i < strings.len() ==> #[trigger] strings[i]@.len() <= usize::MAX
    ensures total_str_len(strings) <= strings.len() * usize::MAX
{
    lemma_spec_sum_bounded(strings.map_values(|s: &str| s@.len()), usize::MAX as nat);
}

fn compute_total_str_len(strings: &Vec<&str>) -> (ret: Option<usize>)
    ensures ret.is_some() ==> ret.unwrap() == total_str_len(strings@)
    ensures ret.is_none() ==> total_str_len(strings@) > usize::MAX
{
    proof { lemma_total_str_len_nonneg(strings@); }
    
    let mut total: usize = 0;
    let mut i = 0;
    
    while i < strings.len()
        invariant 
            0 <= i <= strings.len(),
            total == total_str_len(strings@.subrange(0, i as int)),
            total <= usize::MAX,
    {
        let len = strings[i].len();
        if total > usize::MAX - len {
            proof {
                assert(total + len > usize::MAX);
                assert(total_str_len(strings@.subrange(0, i as int + 1)) == total + len);
                lemma_total_str_len_partial_le_total(strings@, i as int + 1);
            }
            return None;
        }
        total = total + len;
        proof {
            lemma_total_str_len_extend(strings@, i as int);
        }
        i = i + 1;
    }
    
    proof {
        assert(strings@.subrange(0, strings.len() as int) == strings@);
    }
    Some(total)
}

proof fn lemma_total_str_len_extend(strings: Seq<&str>, i: int)
    requires 0 <= i < strings.len()
    ensures total_str_len(strings.subrange(0, i + 1)) == 
            total_str_len(strings.subrange(0, i)) + strings[i]@.len()
{
    let s1 = strings.subrange(0, i);
    let s2 = strings.subrange(0, i + 1);
    assert(s2 == s1.push(strings[i]));
    lemma_spec_sum_push(s1.map_values(|s: &str| s@.len()), strings[i]@.len());
}

proof fn lemma_spec_sum_push(s: Seq<nat>, x: nat)
    ensures spec_sum(s.push(x)) == spec_sum(s) + x
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_spec_sum_push(s.drop_last(), x);
    }
}

proof fn lemma_total_str_len_partial_le_total(strings: Seq<&str>, k: int)
    requires 0 <= k <= strings.len()
    ensures total_str_len(strings.subrange(0, k)) <= total_str_len(strings)
    decreases strings.len() - k
{
    if k == strings.len() {
        assert(strings.subrange(0, k) == strings);
    } else {
        lemma_total_str_len_partial_le_total(strings, k + 1);
        lemma_total_str_len_extend(strings, k);
        lemma_total_str_len_nonneg(seq![strings[k]]);
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
    let len1_opt = compute_total_str_len(&lst1);
    let len2_opt = compute_total_str_len(&lst2);
    
    match (len1_opt, len2_opt) {
        (Some(len1), Some(len2)) => {
            if len1 <= len2 {
                Some(lst1)
            } else {
                Some(lst2)
            }
        },
        _ => None
    }
}
// </vc-code>

fn main() {}
}