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
fn repeat_string(s: String, count: i32) -> (result: String)
    ensures result@ == repeat_string_spec(s@, count as int)
{
    if count <= 0 {
        String::new()
    } else if count == 1 {
        s
    } else {
        let mut res = s.clone();
        let mut remaining = count - 1;
        while remaining > 0
            invariant 
                remaining >= 0,
                res@ == repeat_string_spec(s@, (count - remaining) as int),
            decreases remaining
        {
            res = res + &s;
            remaining = remaining - 1;
        }
        res
    }
}
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
    let n = a.len();
    let mut result = Vec::with_capacity(n);
    let mut idx = 0;
    while idx < n
        invariant 
            n == a.len() && n == i.len(),
            0 <= idx <= n,
            result.len() == idx,
            forall|j: int| 0 <= j < idx ==> 
                result[j]@ == repeat_string_spec(a[j]@, i[j] as int),
        decreases n - idx
    {
        let repeated = repeat_string(a[idx].clone(), i[idx]);
        result.push(repeated);
        idx += 1;
    }
    result
}
// </vc-code>


}
fn main() {}