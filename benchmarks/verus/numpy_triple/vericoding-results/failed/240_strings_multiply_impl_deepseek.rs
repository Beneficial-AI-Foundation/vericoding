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

proof fn repeat_string_lemma(s: Seq<char>, k: int) -> (result: ())
    requires k >= 0
    ensures repeat_string_spec(s, k).len() == k * s.len()
    decreases k
{
    if k > 0 {
        repeat_string_lemma(s, k - 1);
    }
}

proof fn repeat_string_nonnegative(s: Seq<char>, n: int) -> (result: ())
    requires n >= 0
    ensures repeat_string_spec(s, n) == repeat_string_spec(s, n)
    decreases n
{
    if n > 0 {
        repeat_string_nonnegative(s, n - 1);
    }
}

proof fn repeat_string_structural(s: Seq<char>, n: int, m: int) -> (result: ())
    requires n >= 0, m >= 0
    ensures repeat_string_spec(s, n + m) == repeat_string_spec(s, n) + repeat_string_spec(s, m)
    decreases n
{
    if n > 0 {
        repeat_string_structural(s, n - 1, m);
    }
}

/* helper modified by LLM (iteration 5): Added explicit return type annotation to fix compilation */
proof fn repeat_string_zero_case(s: Seq<char>, n: int) -> (result: ())
    requires n <= 0
    ensures repeat_string_spec(s, n) == Seq::<char>::empty()
{
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
    /* code modified by LLM (iteration 5): Fixed compilation error by adding explicit return type annotations */
    let mut result_vec: Vec<String> = Vec::with_capacity(a.len());
    let mut idx: usize = 0;

    while idx < a.len()
        invariant
            result_vec.len() == idx,
            forall|j: int| 0 <= j < result_vec.len() ==> 
                result_vec[j]@ == repeat_string_spec(a[j]@, i[j] as int),
            idx <= a.len()
    {
        let current_string = a[idx].clone();
        let repeat_count = i[idx];
        
        let mut result_string = String::new();
        
        if repeat_count <= 0 {
            // For non-positive counts, always return empty string
            result_string = String::new();
        } else {
            // For positive counts, build the repeated string
            let mut count: i32 = 0;
            while count < repeat_count
                invariant
                    count >= 0,
                    count <= repeat_count,
                    result_string@ == repeat_string_spec(current_string@, count as int)
            {
                result_string.push_str(&current_string);
                count += 1;
            }
        }
        
        result_vec.push(result_string);
        idx += 1;
    }
    
    result_vec
}
// </vc-code>


}
fn main() {}