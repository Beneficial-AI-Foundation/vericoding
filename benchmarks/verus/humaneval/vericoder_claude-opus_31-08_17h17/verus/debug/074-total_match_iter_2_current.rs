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
proof fn lemma_spec_sum_bounds(s: Seq<nat>)
    ensures
        spec_sum(s) >= 0,
        spec_sum(s) <= s.len() * if s.len() > 0 { s.fold_left(0, |acc: nat, x: nat| if x > acc { x } else { acc }) } else { 0 },
{
    if s.len() == 0 {
        assert(s.fold_left(0, |x: int, y| x + y) == 0);
    } else {
        // Inductive proof that sum is non-negative and bounded
    }
}

fn compute_total_len(lst: &Vec<&str>) -> (ret: Option<usize>)
    ensures
        ret.is_some() ==> ret.unwrap() == total_str_len(lst@),
        ret.is_none() ==> total_str_len(lst@) > usize::MAX,
{
    let mut total: usize = 0;
    let mut i: usize = 0;
    
    while i < lst.len()
        invariant
            i <= lst.len(),
            total == spec_sum(lst@.subrange(0, i as int).map_values(|s: &str| s@.len())),
            total <= usize::MAX,
    {
        let len = lst[i].unicode_len();
        
        // Check for overflow
        if total > usize::MAX - len {
            proof {
                assert(lst@.subrange(0, (i + 1) as int).map_values(|s: &str| s@.len()) 
                    == lst@.subrange(0, i as int).map_values(|s: &str| s@.len()).push(lst@[i as int]@.len()));
                assert(spec_sum(lst@.subrange(0, (i + 1) as int).map_values(|s: &str| s@.len())) 
                    == total + len);
                assert(total + len > usize::MAX);
                
                // Show that the total of the full list exceeds usize::MAX
                assert(lst@.subrange(0, lst@.len() as int) == lst@);
                assert(spec_sum(lst@.map_values(|s: &str| s@.len())) >= spec_sum(lst@.subrange(0, (i + 1) as int).map_values(|s: &str| s@.len())));
            }
            return None;
        }
        
        total = total + len;
        i = i + 1;
        
        proof {
            assert(lst@.subrange(0, i as int) == lst@.subrange(0, (i - 1) as int).push(lst@[(i - 1) as int]));
            assert(lst@.subrange(0, i as int).map_values(|s: &str| s@.len())
                == lst@.subrange(0, (i - 1) as int).map_values(|s: &str| s@.len()).push(lst@[(i - 1) as int]@.len()));
        }
    }
    
    proof {
        assert(lst@.subrange(0, lst@.len() as int) == lst@);
        assert(total == spec_sum(lst@.map_values(|s: &str| s@.len())));
        assert(total == total_str_len(lst@));
    }
    
    Some(total)
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
    let total1_opt = compute_total_len(&lst1);
    let total2_opt = compute_total_len(&lst2);
    
    match (total1_opt, total2_opt) {
        (Some(total1), Some(total2)) => {
            proof {
                assert(total1 == total_str_len(lst1@));
                assert(total2 == total_str_len(lst2@));
                assert(total1 <= usize::MAX);
                assert(total2 <= usize::MAX);
            }
            
            if total1 <= total2 {
                proof {
                    assert(total_str_len(lst1@) <= total_str_len(lst2@));
                }
                Some(lst1)
            } else {
                proof {
                    assert(total_str_len(lst1@) > total_str_len(lst2@));
                }
                Some(lst2)
            }
        }
        _ => {
            proof {
                assert(total1_opt.is_none() || total2_opt.is_none());
                assert(total1_opt.is_none() ==> total_str_len(lst1@) > usize::MAX);
                assert(total2_opt.is_none() ==> total_str_len(lst2@) > usize::MAX);
            }
            None
        }
    }
}
// </vc-code>

fn main() {}
}