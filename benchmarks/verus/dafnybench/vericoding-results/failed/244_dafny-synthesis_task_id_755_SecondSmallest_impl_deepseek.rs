use vstd::prelude::*;

verus! {

spec fn min_pair(s: Seq<i32>) -> i32 {
    if s[0] <= s[1] { s[0] } else { s[1] }
}

spec fn min(s: Seq<i32>) -> i32;

// <vc-helpers>
spec fn min(s: Seq<i32>) -> i32 {
    decreases(s.len());
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        s[0]
    } else {
        let m = min(s.subrange(1, s.len() as int));
        if s[0] <= m { s[0] } else { m }
    }
}

proof fn min_exists_in_nonempty_seq(s: Seq<i32>, i: int)
    requires
        s.len() >= 1,
        0 <= i < s.len()
    ensures
        s@[i] >= min(s@)
{
}

proof fn min_is_less_than_or_equal_to_all(s: Seq<i32>, k: int)
    requires
        0 <= k < s.len()
    ensures
        min(s@) <= s@[k]
{
    if s.len() == 0 {
    } else if s.len() == 1 {
    } else {
        let m = min(s.subrange(1, s.len() as int));
        if s[0] <= m {
            if k == 0 {
            } else {
                min_is_less_than_or_equal_to_all(s.subrange(1, s.len() as int), k-1);
            }
        } else {
            min_is_less_than_or_equal_to_all(s.subrange(1, s.len() as int), k-1);
        }
    }
}

spec fn second_min(s: Seq<i32>) -> i32
    recommends s.len() >= 2
{
    let filtered = s.filter(|&x| x != min(s));
    if filtered.len() == 0 {
        min(s)
    } else {
        min(filtered)
    }
}

proof fn second_smallest_exists(s: Seq<i32>)
    requires
        s.len() >= 2,
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && 
            s@[i] == min(s@) && s@[j] != s@[i]
    ensures
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && 
            s@[i] == min(s@) && s@[j] == second_min(s@)
{
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &[i32]) -> (second_smallest: i32)
    requires 
        s.len() >= 2,
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && 
            s[i] == min(s@) && s[j] != s[i]
    ensures 
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && 
            s[i] == min(s@) && s[j] == second_smallest,
        forall|k: int| 0 <= k < s.len() && s[k] != min(s@) ==> s[k] >= second_smallest
// </vc-spec>
// <vc-code>
{
    let mut min_val = i32::MAX;
    let mut second_min_val = i32::MAX;
    
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            min_val >= min(s@),
            second_min_val >= min(s@),
            (min_val == i32::MAX || min_val == min(s@)),
            forall|k: int| 0 <= k < i ==> s[k] >= min_val,
            forall|k: int| 0 <= k < i && s[k] != min(s@) ==> s[k] >= second_min_val,
            exists|k: int| 0 <= k < s.len() && s[k] == min(s@)
    {
        let current = s[i];
        if current < min_val {
            second_min_val = min_val;
            min_val = current;
        } else if current != min_val && (current < second_min_val || second_min_val == min_val) {
            second_min_val = current;
        }
        
        i += 1;
    }
    
    proof {
        second_smallest_exists(s@);
    }
    
    second_min_val
}
// </vc-code>

fn main() {
}

}