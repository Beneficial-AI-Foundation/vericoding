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

proof fn lemma_min_is_minimum(s: Seq<i32>, i: int)
    requires s.len() > 0, 0 <= i < s.len()
    ensures s[i] >= min(s)
    decreases s.len()
{
    if s.len() == 1 {
        // base case
    } else {
        let rest = s.subrange(1, s.len() as int);
        if i == 0 {
            if s[0] <= min(rest) {
                // s[0] is the minimum
            } else {
                lemma_min_is_minimum(rest, 0);
            }
        } else {
            lemma_min_is_minimum(rest, i - 1);
            if s[0] <= min(rest) {
                // min(s) == s[0]
            } else {
                // min(s) == min(rest)
            }
        }
    }
}

proof fn lemma_min_exists(s: Seq<i32>)
    requires s.len() > 0
    ensures exists|i: int| 0 <= i < s.len() && s[i] == min(s)
    decreases s.len()
{
    if s.len() == 1 {
        // base case
    } else {
        let rest = s.subrange(1, s.len() as int);
        lemma_min_exists(rest);
        if s[0] <= min(rest) {
            // s[0] is the minimum
        } else {
            // min(rest) is the minimum
        }
    }
}

proof fn lemma_min_subrange(s: Seq<i32>, end: int)
    requires 0 < end <= s.len()
    ensures min(s.subrange(0, end)) <= min(s.subrange(0, end + 1))
    decreases end
{
    if end == s.len() {
        // nothing to prove
    } else {
        let sub1 = s.subrange(0, end);
        let sub2 = s.subrange(0, end + 1);
        if end == 1 {
            // base case
        } else {
            lemma_min_subrange(s, end - 1);
        }
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    proof {
        lemma_min_exists(s@);
    }
    
    let mut first_min = s[0];
    let mut second_min = i32::MAX;
    let mut found_different = false;
    
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            i > 0 ==> first_min == min(s@.subrange(0, i as int)),
            found_different ==> (exists|j: int| 0 <= j < i && s[j] != first_min),
            found_different ==> (forall|j: int| 0 <= j < i && s[j] != first_min ==> s[j] >= second_min),
            found_different ==> (exists|j: int| 0 <= j < i && s[j] == second_min && s[j] != first_min)
    {
        if i == 0 {
            first_min = s[i];
        } else {
            proof {
                lemma_min_subrange(s@, i as int);
            }
            
            if s[i] < first_min {
                if found_different {
                    second_min = first_min;
                }
                found_different = true;
                first_min = s[i];
            } else if s[i] != first_min {
                if !found_different {
                    second_min = s[i];
                    found_different = true;
                } else if s[i] < second_min {
                    second_min = s[i];
                }
            }
        }
        i += 1;
    }
    
    proof {
        assert(first_min == min(s@));
    }
    
    second_min
}
// </vc-code>

fn main() {
}

}