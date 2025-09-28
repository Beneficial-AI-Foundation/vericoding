// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_rec(a: Seq<int>, x: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0int
    } else {
        count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1int } else { 0int })
    }
}

/* helper modified by LLM (iteration 5): fixed integer literal type annotations */
proof fn count_rec_properties(a: Seq<int>, x: int)
    ensures
        count_rec(a, x) >= 0,
        count_rec(a, x) <= a.len(),
        count_rec(seq![], x) == 0,
        a.len() > 0 ==> count_rec(a, x) == count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1int } else { 0int })
    decreases a.len()
{
    if a.len() == 0 {
    } else {
        count_rec_properties(a.subrange(1, a.len() as int), x);
    }
}

proof fn count_rec_contains(a: Seq<int>, x: int)
    ensures
        a.contains(x) <==> count_rec(a, x) >= 1,
        count_rec(a, x) == 1 <==> (a.contains(x) && forall|i: int, j: int| 0 <= i < j < a.len() && a[i] == x ==> a[j] != x)
    decreases a.len()
{
    if a.len() == 0 {
    } else {
        count_rec_contains(a.subrange(1, a.len() as int), x);
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: Vec<i8>) -> (result: Vec<i8>)
    requires 
        forall|i: int| 0 <= i < a@.len() ==> count_rec(a@.map(|_i: int, x: i8| x as int), a@[i] as int) >= 1
    ensures 
        forall|i: int| 0 <= i < result@.len() ==> count_rec(a@.map(|_i: int, x: i8| x as int), result@[i] as int) == 1,
        forall|i: int| 0 <= i < a@.len() ==> (result@.map(|_i: int, x: i8| x as int).contains(a@[i] as int) <==> count_rec(a@.map(|_i: int, x: i8| x as int), a@[i] as int) == 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved ghost computations into proof blocks */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < result@.len() ==> count_rec(a@.map(|_k: int, x: i8| x as int), result@[j] as int) == 1,
            forall|j: int| 0 <= j < i ==> (result@.map(|_k: int, x: i8| x as int).contains(a@[j] as int) <==> count_rec(a@.map(|_k: int, x: i8| x as int), a@[j] as int) == 1)
    {
        let current = a[i];
        
        proof {
            let ghost_count = count_rec(a@.map(|_k: int, x: i8| x as int), current as int);
            if ghost_count == 1 {
                result.push(current);
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}