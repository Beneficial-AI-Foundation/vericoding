// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(diameters: Seq<int>) -> bool {
    diameters.len() > 0 && forall|i: int| 0 <= i < diameters.len() ==> diameters[i] > 0
}

spec fn num_distinct(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.subrange(1, s.len() as int).contains(s[0]) {
        num_distinct(s.subrange(1, s.len() as int))
    } else {
        1 + num_distinct(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(diameters: Vec<i8>) -> (result: i8)
    requires 
        valid_input(diameters@.map(|i, x| x as int)),
    ensures 
        result as int == num_distinct(diameters@.map(|i, x| x as int)),
        result as int >= 1,
        result as int <= diameters@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed trigger placement - triggers should be on simple expressions */
    let mut seen = Vec::new();
    let mut count: i8 = 0;
    let mut i: usize = 0;
    
    while i < diameters.len()
        invariant
            0 <= i <= diameters.len(),
            0 <= count as int <= i,
            count as int <= seen.len(),
            seen@.len() <= i,
            forall|j: int| 0 <= j < seen@.len() ==> seen@[j] as int > 0,
            forall|j: int| 0 <= j < seen@.len() ==> exists|k: int| 0 <= k < i && diameters@[k] == seen@[j],
            forall|j: int, k: int| 0 <= j < k < seen@.len() ==> seen@[j] != seen@[k],
            count as int == seen@.len(),
            count as int == num_distinct(diameters@.subrange(0, i as int).map(|idx, x| x as int)),
        decreases diameters.len() - i
    {
        let current = diameters[i];
        let mut found = false;
        let mut j: usize = 0;
        
        while j < seen.len()
            invariant
                0 <= j <= seen.len(),
                found ==> exists|k: int| 0 <= k < j && seen@[k] == current,
                !found ==> forall|k: int| 0 <= k < j ==> seen@[k] != current,
            decreases seen.len() - j
        {
            if seen[j] == current {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        if !found {
            seen.push(current);
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}