use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_min_second_value(s: &Vec<Vec<i32>>, min_idx: int)
    requires
        0 <= min_idx < s.len(),
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s@[i].len() >= 2,
        forall|j: int| 0 <= j < s.len() ==> s@[min_idx]@[1] <= s@[j]@[1],
    ensures
        exists|i: int| 0 <= i < s.len() && s@[i]@[0] == s@[min_idx]@[0] && 
            forall|j: int| 0 <= j < s.len() ==> s@[i]@[1] <= s@[j]@[1],
{
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
fn min_second_value_first(s: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    requires 
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s@[i].len() >= 2,
    ensures 
        exists|i: int| 0 <= i < s.len() && first_of_min_second == s@[i]@[0] && 
            forall|j: int| 0 <= j < s.len() ==> s@[i]@[1] <= s@[j]@[1],
{
    let mut min_idx: usize = 0;
    let mut i: usize = 1;

    while i < s.len()
        invariant
            0 <= min_idx < s.len(),
            1 <= i <= s.len(),
            forall|j: int| 0 <= j < i as int ==> s@[min_idx as int]@[1] <= s@[j]@[1],
    {
        if s@[i]@[1] < s@[min_idx]@[1] {
            min_idx = i;
        }
        i = i + 1;
    }

    proof {
        lemma_min_second_value(s, min_idx as int);
    }

    s@[min_idx]@[0]
}
// </vc-code>

fn main() {
}

}