use vstd::prelude::*;

verus! {

spec fn min_pair(s: Seq<i32>) -> i32 {
    if s[0] <= s[1] { s[0] } else { s[1] }
}

spec fn min(s: Seq<i32>) -> i32;

// <vc-helpers>
spec fn min(s: Seq<i32>) -> i32 
    decreases s.len()
{
    if s.len() == 0 {
        0  // arbitrary value for empty sequence
    } else if s.len() == 1 {
        s[0]
    } else {
        let rest_min = min(s.subrange(1, s.len() as int));
        if s[0] <= rest_min { s[0] } else { rest_min }
    }
}

proof fn min_is_minimum(s: Seq<i32>)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> s[i] >= min(s)
    ensures exists|i: int| 0 <= i < s.len() && s[i] == min(s)
    decreases s.len()
{
    if s.len() == 1 {
        // base case
    } else {
        let rest = s.subrange(1, s.len() as int);
        min_is_minimum(rest);
        
        if s[0] <= min(rest) {
            // min(s) == s[0]
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] >= min(rest) >= s[0]);
        } else {
            // min(s) == min(rest)
            assert(exists|j: int| 1 <= j < s.len() && s[j] == min(rest));
        }
    }
}

proof fn min_in_subrange(s: Seq<i32>, start: int, end: int)
    requires 0 <= start < end <= s.len()
    ensures min(s.subrange(start, end)) >= min(s)
    decreases s.len()
{
    min_is_minimum(s);
    min_is_minimum(s.subrange(start, end));
}

proof fn min_subrange_extend(s: Seq<i32>, i: int)
    requires 0 < i <= s.len()
    ensures min(s.subrange(0, i)) == min(s@.subrange(0, i))
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
    proof {
        min_is_minimum(s@);
    }
    
    let mut smallest = if s[0] <= s[1] { s[0] } else { s[1] };
    let mut second_smallest = if s[0] <= s[1] { s[1] } else { s[0] };
    
    let mut i = 2;
    while i < s.len()
        invariant 
            2 <= i <= s.len(),
            smallest == min(s@.subrange(0, i as int)),
            forall|k: int| 0 <= k < i && s@[k] != smallest ==> s@[k] >= second_smallest,
            exists|k: int| 0 <= k < i && s@[k] == second_smallest && s@[k] != smallest
    {
        proof {
            min_is_minimum(s@.subrange(0, i as int));
            min_is_minimum(s@.subrange(0, (i + 1) as int));
        }
        
        if s[i] < smallest {
            second_smallest = smallest;
            smallest = s[i];
        } else if s[i] < second_smallest && s[i] != smallest {
            second_smallest = s[i];
        }
        i += 1;
    }
    
    proof {
        assert(smallest == min(s@.subrange(0, s.len() as int)));
        assert(s@.subrange(0, s.len() as int) =~= s@);
        assert(smallest == min(s@));
        min_is_minimum(s@);
    }
    
    second_smallest
}
// </vc-code>

fn main() {
}

}