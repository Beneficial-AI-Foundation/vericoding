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
        // Prove by induction
        let n = s.len();
        if n == 1 {
            assert(spec_sum(s) == s[0]);
            assert(s[0] >= 0);
            let max = s.fold_left(0, |acc: nat, x: nat| if x > acc { x } else { acc });
            assert(max >= s[0]);
            assert(spec_sum(s) <= max);
        } else {
            let s_init = s.subrange(0, n - 1);
            lemma_spec_sum_bounds(s_init);
            
            let last = s[n - 1];
            assert(s == s_init.push(last));
            assert(spec_sum(s) == spec_sum(s_init) + last);
            assert(spec_sum(s) >= 0);
            
            let max_full = s.fold_left(0, |acc: nat, x: nat| if x > acc { x } else { acc });
            let max_init = s_init.fold_left(0, |acc: nat, x: nat| if x > acc { x } else { acc });
            assert(max_full >= max_init);
            assert(max_full >= last);
            
            // Each element is at most max_full
            assert forall|i: int| 0 <= i < s.len() implies s[i] <= max_full by {
                if i < s_init.len() {
                    assert(s[i] == s_init[i]);
                } else {
                    assert(s[i] == last);
                }
            }
            assert(spec_sum(s) <= s.len() * max_full);
        }
    }
}

proof fn lemma_sum_push(s: Seq<nat>, x: nat)
    ensures spec_sum(s.push(x)) == spec_sum(s) + x
{
    // This follows from the definition of fold_left
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
        decreases lst.len() - i,
    {
        let len = lst[i].unicode_len();
        
        // Check for overflow
        if total > usize::MAX - len {
            proof {
                let prefix = lst@.subrange(0, i as int).map_values(|s: &str| s@.len());
                let next_prefix = lst@.subrange(0, (i + 1) as int).map_values(|s: &str| s@.len());
                
                assert(lst@.subrange(0, (i + 1) as int) == lst@.subrange(0, i as int).push(lst@[i as int]));
                assert(next_prefix == prefix.push(lst@[i as int]@.len()));
                
                lemma_sum_push(prefix, lst@[i as int]@.len());
                assert(spec_sum(next_prefix) == spec_sum(prefix) + lst@[i as int]@.len());
                assert(spec_sum(next_prefix) == total + len);
                assert(spec_sum(next_prefix) > usize::MAX);
                
                // Show that the total of the full list exceeds usize::MAX
                assert(lst@.subrange(0, lst@.len() as int) == lst@);
                
                // The full sum includes everything in next_prefix
                assert forall|j: int| 0 <= j <= i implies 
                    lst@.map_values(|s: &str| s@.len())[j] == next_prefix[j] by {
                    assert(lst@[j] == lst@.subrange(0, (i + 1) as int)[j]);
                }
                
                lemma_spec_sum_bounds(lst@.map_values(|s: &str| s@.len()));
                lemma_spec_sum_bounds(next_prefix);
                
                // Since next_prefix is a prefix of the full sequence
                assert(total_str_len(lst@) >= spec_sum(next_prefix));
                assert(total_str_len(lst@) > usize::MAX);
            }
            return None;
        }
        
        total = total + len;
        i = i + 1;
        
        proof {
            let old_i = (i - 1) as int;
            let new_i = i as int;
            
            assert(lst@.subrange(0, new_i) == lst@.subrange(0, old_i).push(lst@[old_i]));
            
            let old_mapped = lst@.subrange(0, old_i).map_values(|s: &str| s@.len());
            let new_mapped = lst@.subrange(0, new_i).map_values(|s: &str| s@.len());
            
            assert(new_mapped == old_mapped.push(lst@[old_i]@.len()));
            
            lemma_sum_push(old_mapped, lst@[old_i]@.len());
            assert(spec_sum(new_mapped) == spec_sum(old_mapped) + lst@[old_i]@.len());
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