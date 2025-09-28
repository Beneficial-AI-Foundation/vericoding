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
/* helper modified by LLM (iteration 4): [fixed compilation error by replacing unsupported `String::new()` with `"".to_string()`] */
fn repeat_string(s: &String, n: i32) -> (result: String)
    ensures
        result@ == repeat_string_spec(s@, n as int),
    decreases (if n <= 0 { 0 } else { n }) as nat
{
    if n <= 0 {
        "".to_string()
    } else {
        let mut res = s.clone();
        let rest = repeat_string(s, n - 1);
        res.push_str(rest.as_str());
        res
    }
}

#[verifier::spinoff_prover]
proof fn lemma_repeat_empty_is_empty(n: int)
    ensures
        repeat_string_spec(Seq::<char>::empty(), n) == Seq::<char>::empty(),
    decreases (if n <= 0 { 0 } else { n }) as nat
{
    if n > 0 {
        lemma_repeat_empty_is_empty(n - 1);
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
/* code modified by LLM (iteration 4): [no logical change, kept as is since error was in helper] */
{
    let mut result: Vec<String> = Vec::new();
    let mut j: usize = 0;
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            a.len() == i.len(),
            result.len() == j,
            forall|k: int| 0 <= k < j as int ==> 
                result[k]@ == repeat_string_spec(a[k]@, i[k] as int),
        decreases a.len() - j
    {
        let s = &a[j];
        let n = i[j];

        let repeated_s = repeat_string(s, n);
        result.push(repeated_s);
        j = j + 1;
    }
    result
}
// </vc-code>


}
fn main() {}