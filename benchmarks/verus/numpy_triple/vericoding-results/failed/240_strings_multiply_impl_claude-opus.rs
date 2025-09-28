// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn repeat_string_spec(s: Seq<char>, n: int) -> Seq<char> 
    decreases (if n <= 0 { 0 } else { n }) as nat
{
    if n <= 0 {
        Seq::<char>::empty()
    } else if n == 1 {
        s
    } else {
        s + repeat_string_spec(s, n - 1)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn multiply(a: Vec<String>, i: Vec<i32>) -> (result: Vec<String>)
    requires a.len() == i.len(),
    ensures 
        result.len() == a.len(),
        /* Core property: Element-wise string repetition */
        forall|j: int| 0 <= j < a.len() ==> 
            result[j]@ == repeat_string_spec(a[j]@, i[j] as int),
        /* Zero/negative repetition property: Always yields empty string */
        forall|j: int| 0 <= j < a.len() && i[j] <= 0 ==> 
            result[j]@ == Seq::<char>::empty(),
        /* Identity property: Multiplying by 1 yields the original string */
        forall|j: int| 0 <= j < a.len() && i[j] == 1 ==> 
            result[j] == a[j],
        /* Zero property: Multiplying by 0 yields empty string */
        forall|j: int| 0 <= j < a.len() && i[j] == 0 ==> 
            result[j]@ == Seq::<char>::empty(),
        /* Empty string property: Empty strings remain empty regardless of repetition */
        forall|j: int| 0 <= j < a.len() && a[j]@ == Seq::<char>::empty() ==> 
            result[j]@ == Seq::<char>::empty(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Using String::new() instead of non-existent new_strlit */
    let mut result: Vec<String> = Vec::new();
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            a.len() == i.len(),
            result.len() == idx,
            forall|j: int| 0 <= j < idx ==> result[j]@ == repeat_string_spec(a[j]@, i[j] as int),
        decreases a.len() - idx
    {
        let s = &a[idx];
        let count = i[idx];
        
        if count <= 0 {
            result.push(String::new());
        } else if count == 1 {
            result.push(s.clone());
        } else {
            let mut repeated = String::new();
            let mut k = 0;
            
            while k < count
                invariant
                    0 <= k <= count,
                    count > 1,
                    repeated@ == repeat_string_spec(s@, k as int),
                decreases count - k
            {
                repeated.push_str(s);
                k += 1;
            }
            
            result.push(repeated);
        }
        
        idx += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}