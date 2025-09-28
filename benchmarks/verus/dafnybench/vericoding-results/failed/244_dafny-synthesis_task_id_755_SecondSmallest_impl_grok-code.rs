use vstd::prelude::*;

verus! {

spec fn min_pair(s: Seq<i32>) -> i32 {
    if s[0] <= s[1] { s[0] } else { s[1] }
}

spec fn min(s: Seq<i32>) -> i32;

// <vc-helpers>
spec fn min_pair(s: Seq<i32>) -> i32 {
    if s[0] <= s[1] { s[0] } else { s[1] }
}

spec fn min(s: Seq<i32>) -> i32 {
    if s.len() == 0 { -1 } else if s.len() == 1 { s[0] } else {
        let rest_min = min(s.drop(1));
        if s[0] <= rest_min { s[0] } else { rest_min }
    }
}

proof fn min_definition(s: Seq<i32>)
    ensures 
        forall|i: int| 0 <= i < s.len() ==> s[i] >= min(s)
    decreases(s.len())
{
    if s.len() == 0 {
        
    } else if s.len() == 1 {
        // trivial
    } else {
        min_definition(s.drop(1));
    }
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
    let mut min1 = i32::MAX;
    let mut min2 = i32::MAX;
    let mut i = 0;
    while i < s.len()
        invariant (0 <= i <= s.len() as int);
        invariant (min1 <= min2);
        invariant (forall|j: int| 0 <= j < i ==> s@[j] >= min1);
        invariant (min2 < i32::MAX ==> min2 > min1);
        invariant (min2 < i32::MAX ==> (exists|k: int| 0 <= k < i && s@[k] == min2));
    {
        if s[i] < min1 {
            min2 = min1;
            min1 = s[i];
        } else if s[i] < min2 && s[i] != min1 {
            min2 = s[i];
        }
        i += 1;
    }
    proof {
        min_definition(s@);
        assert(min(s@) == min1);
        assert(min2 != i32::MAX);
        assert(forall|j: int| 0 <= j < s.len() && s@[j] != min(s@) ==> s@[j] >= min2);
        assert(exists|j: int| 0 <= j < s.len() && s@[j] == min(s@));
        assert(exists|j: int| 0 <= j < s.len() && s@[j] == min2 && s@[j] != min(s@));
    }
    min2
}
// </vc-code>

fn main() {
}

}