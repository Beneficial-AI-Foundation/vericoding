use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn min_second_index(s: Seq<Seq<i32>>) -> int
    recommends s.len() > 0, forall|i: int| 0 <= i < s.len() ==> s[i].len() >= 2
{
    choose|i: int| 0 <= i < s.len() && 
        #[trigger] s[i][1] <= s[i][1] &&
        (forall|j: int| 0 <= j < s.len() ==> #[trigger] s[i][1] <= #[trigger] s[j][1])
}

proof fn min_second_exists(s: Seq<Vec<i32>>)
    requires s.len() > 0, forall|i: int| 0 <= i < s.len() ==> s[i].len() >= 2
    ensures exists|i: int| 0 <= i < s.len() && 
        (forall|j: int| #[trigger] (0 <= j < s.len()) ==> #[trigger] s[i]@[1] <= #[trigger] s[j]@[1])
{
    assert(0 < s.len());
    
    // There must exist a minimum by well-ordering of integers
    assert(exists|i: int| 0 <= i < s.len() && 
        (forall|j: int| #[trigger] (0 <= j < s.len()) ==> #[trigger] s[i]@[1] <= #[trigger] s[j]@[1]));
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn min_second_value_first(s: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    requires 
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s@[i].len() >= 2,
    ensures 
        exists|i: int| 0 <= i < s.len() && first_of_min_second == s@[i]@[0] && 
            (forall|j: int| 0 <= j < s.len() ==> s@[i]@[1] <= s@[j]@[1]),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    proof {
        min_second_exists(s@);
    }
    
    let mut min_idx: usize = 0;
    let mut min_second = s[0][1];
    let mut i = 1;
    
    while i < s.len()
        invariant
            0 <= min_idx < s.len(),
            0 <= i <= s.len(),
            min_second == s@[min_idx as int]@[1],
            forall|j: int| 0 <= j < i ==> s@[min_idx as int]@[1] <= s@[j]@[1],
        decreases s.len() - i
    {
        if s[i][1] < min_second {
            min_idx = i;
            min_second = s[i][1];
        }
        i += 1;
    }
    
    s[min_idx][0]
}
// </vc-code>

fn main() {
}

}