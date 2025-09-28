// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added count_rec function definition */
spec fn count_rec(a: Seq<int>, x: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0int
    } else {
        count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1int } else { 0int })
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
    /* code modified by LLM (iteration 5): Added trigger annotations to fix quantifier inference */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result@.len() <= i,
            forall|j: int, k: int| 0 <= j < k < result@.len() ==> result@[j] != result@[k],
            forall|j: int| #[trigger] (0 <= j < result@.len()) ==> exists|k: int| 0 <= k < i && a@[k] == result@[j],
            forall|j: int| 0 <= j < i ==> (result@.contains(a@[j]) <==> !exists|k: int| 0 <= k < j && a@[k] == a@[j])
        decreases a.len() - i
    {
        let val = a[i];
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant_except_break
                0 <= j <= result.len(),
                found <==> exists|k: int| 0 <= k < j && result@[k] == val
            ensures
                found <==> result@.contains(val)
            decreases result.len() - j
        {
            if result[j] == val {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        if !found {
            result.push(val);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}