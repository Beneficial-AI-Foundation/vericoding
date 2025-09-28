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
proof fn lemma_seq_map_distinct(s: Seq<int>) -> (distinct: int)
    ensures distinct == num_distinct(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let head = s[0];
        let tail = s.subrange(1, s.len() as int);
        let tail_distinct = lemma_seq_map_distinct(tail);
        if tail.contains(head) {
            tail_distinct
        } else {
            tail_distinct + 1
        }
    }
}

fn count_distinct(vec: Vec<i8>) -> (count: i8)
    requires
        vec@.len() > 0,
        forall|i: int| 0 <= i < vec@.len() ==> vec@[i] > 0,
    ensures
        count as int == num_distinct(vec@.map(|i, x| x as int)),
        count >= 1,
        count <= (vec@.len() as i8)
{
    let mut seen = Vec::<int>::new();
    let mut result = 0;
    
    proof {
        lemma_seq_map_distinct(vec@.map(|i, x| x as int));
    }
    
    let mut i = 0;
    while i < vec.len()
        invariant
            0 <= i <= vec@.len(),
            seen@.len() == i,
            result as int == num_distinct(seen@),
            forall|j: int| 0 <= j < i ==> seen@[j] == vec@[j] as int,
            1 <= result,
            result <= (vec@.len() as i8)
        decreases vec@.len() - i
    {
        let current = vec[i] as int;
        let mut found = false;
        let mut j = 0;
        
        while j < seen.len()
            invariant
                0 <= j <= seen@.len(),
                found == exists|k: nat| j <= k < seen@.len() && seen@[k] == current,
            decreases seen@.len() - j
        {
            if seen[j] == current {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            proof {
                assert(seen@.subrange(0, seen@.len()).contains(current) == found);
            }
            result = (result + 1) as i8;
        }
        
        seen.push(current);
        i += 1;
    }
    
    result
}
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
    /* code modified by LLM (iteration 5): Fixed compilation error by using ghost variable */
    ghost {
        let vec = diameters@.map(|i, x| x as int);
    }
    let distinct_count = count_distinct(diameters);
    distinct_count
}
// </vc-code>


}

fn main() {}