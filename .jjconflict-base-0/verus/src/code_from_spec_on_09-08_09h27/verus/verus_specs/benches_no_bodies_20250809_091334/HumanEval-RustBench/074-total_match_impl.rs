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
    if i == j {
        // Base case: subranges are identical
        assert(s.subrange(0, i) =~= s.subrange(0, j));
    } else {
        // Inductive case: j > i
        lemma_increasing_sum(s, i, j - 1);
        
        // Show that adding one more element increases the sum
        let sub_i = s.subrange(0, i);
        let sub_j_minus_1 = s.subrange(0, j - 1);
        let sub_j = s.subrange(0, j);
        
        // sub_j is sub_j_minus_1 with s[j-1] added
        assert(sub_j =~= sub_j_minus_1.push(s[j - 1]));
        
        // The sum increases by s[j-1] which is non-negative
        assert(spec_sum(sub_j) == spec_sum(sub_j_minus_1) + s[j - 1]);
        assert(spec_sum(sub_i) <= spec_sum(sub_j_minus_1));
        assert(s[j - 1] >= 0);
    }
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
            total as int == total_str_len(lst@.subrange(0, i as int)),
            total <= usize::MAX,
    {
        /* code modified by LLM (iteration 1): convert nat to usize for arithmetic operations */
        let str_len = lst[i]@.len();
        let str_len_usize = str_len as usize;
        
        // Check for overflow
        if total > usize::MAX - str_len_usize {
            proof {
                // Overflow would occur
                assert(total as int + str_len as int > usize::MAX);
                // Show that the total would exceed usize::MAX
                assert(total_str_len(lst@.subrange(0, i as int + 1)) == 
                       total_str_len(lst@.subrange(0, i as int)) + lst@[i as int]@.len());
                assert(total_str_len(lst@.subrange(0, i as int + 1)) > usize::MAX);
                
                lemma_increasing_sum(
                    lst@.map_values(|s: &str| s@.len()),
                    i as int + 1,
                    lst.len() as int
                );
            }
            
            return None;
        }
        
        /* code modified by LLM (iteration 1): use converted usize value for addition */
        total = total + str_len_usize;
        i = i + 1;
    }
    
    assert(i == lst.len());
    assert(total as int == total_str_len(lst@));
    
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
    let len1_opt = checked_total_str_len(&lst1);
    let len2_opt = checked_total_str_len(&lst2);
    
    match (len1_opt, len2_opt) {
        (Some(len1), Some(len2)) => {
            if len1 <= len2 {
                Some(lst1)
            } else {
                Some(lst2)
            }
        },
        _ => None,
    }
}

}
fn main() {}