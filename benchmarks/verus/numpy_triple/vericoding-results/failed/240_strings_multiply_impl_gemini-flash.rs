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
/* helper modified by LLM (iteration 5): The `string_repeat_helper` was updated to accept `i32` for `n` and internally cast it to `usize` for `s.repeat`. The `requires` clause was also updated to explicitly ensure `n` is non-negative, aligning with the external `String::repeat` function's expectations. */
#[verifier(external_body)]
fn string_repeat_helper(s: &String, n: i32) -> String
    requires
        n >= 0,
{
    s.repeat(n as usize)
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
/* code modified by LLM (iteration 5): The conditions in the `proof` block were restructured to cast `i[k]` to `int` for comparisons immediately, resolving type mismatch errors. The `string_repeat_helper` now handles negative `i[k]` by directly returning an empty string, avoiding invalid `usize` conversions, and it ensures `i[k]` is passed as `i32` to the helper function. */
{
    let mut result: Vec<String> = Vec::new();
    let mut k = 0;
    while k < a.len()
        invariant
            0 <= k && k <= a.len(),
            result.len() == k,
            forall|j: int| 0 <= j < k ==> result[j]@ == repeat_string_spec(a[j]@, i[j] as int),
        decreases a.len() - k
    {
        proof {
            if (i[k] as int) < 0 {
                assert(repeat_string_spec(a[k]@, i[k] as int) == Seq::<char>::empty());
            } else if (i[k] as int) == 0 {
                assert(repeat_string_spec(a[k]@, i[k] as int) == Seq::<char>::empty());
            } else if (i[k] as int) == 1 {
                assert(repeat_string_spec(a[k]@, i[k] as int) == a[k]@);
            }
        }

        let repeated_string = if i[k] < 0 {
            String::new()
        } else {
            string_repeat_helper(&a[k], i[k])
        };
        result.push(repeated_string);
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}