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
/* helper modified by LLM (iteration 5): Changed string concatenation to push_str to avoid Verus codegen error */
fn repeat_string_exec(s: String, n: i32) -> (result: String)
    requires n >= 0,
    ensures result@ == repeat_string_spec(s@, n as int),
{
    let mut result: String = "".to_string();
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i <= (n as usize),
            result@ == repeat_string_spec(s@, i as int),
        decreases (n as usize) - i
    {
        result.push_str(&s);
        i += 1;
    }
    result
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
    /* code modified by LLM (iteration 3): Fixed compilation error by replacing String::new() with "".to_string() */
    let mut result: Vec<String> = Vec::with_capacity(a.len());
    let mut j: usize = 0;
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            result.len() == j,
            forall |k: int| 0 <= k < j ==> result[k]@ == repeat_string_spec(a[k]@, i[k] as int),
        decreases a.len() - j
    {
        let n = i[j];
        if n <= 0 {
            result.push("".to_string());
        } else {
            let rep = repeat_string_exec(a[j].clone(), n);
            result.push(rep);
        }
        j += 1;
    }
    result
}
// </vc-code>


}
fn main() {}