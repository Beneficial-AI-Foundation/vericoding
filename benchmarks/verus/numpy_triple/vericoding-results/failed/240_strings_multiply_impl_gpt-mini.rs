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
/* helper modified by LLM (iteration 5): runtime repeat using i32 */
fn repeat_string_runtime(s: String, n: i32) -> (result: String)
    requires
        n >= 0,
    ensures
        result@ == repeat_string_spec(s@, n as int),
{
    let mut res = String::new();
    let mut k: i32 = 0;
    while k < n
        invariant
            0 <= k && k <= n,
            res@ == repeat_string_spec(s@, k as int),
        decreases (n - k) as nat
    {
        let old_res = res.clone();
        res = old_res + s.as_str();
        k += 1;
    }
    res
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
/* code modified by LLM (iteration 5): iterate and use repeat_string_runtime with i32 indices */
{
    let mut result_vec: Vec<String> = Vec::new();
    let len: usize = a.len();
    let mut idx: usize = 0;
    while idx < len
        invariant
            0 <= idx as int && idx as int <= len as int,
            result_vec.len() == idx,
            forall|j: int| 0 <= j < idx as int ==> result_vec@[j]@ == repeat_string_spec(a@[j]@, i@[j] as int),
        decreases (len - idx) as nat
    {
        let s = a[idx].clone();
        let times: i32 = i[idx];
        let r = if times <= 0 {
            String::new()
        } else if times == 1 {
            s.clone()
        } else {
            repeat_string_runtime(s.clone(), times)
        };
        result_vec.push(r);
        idx += 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}