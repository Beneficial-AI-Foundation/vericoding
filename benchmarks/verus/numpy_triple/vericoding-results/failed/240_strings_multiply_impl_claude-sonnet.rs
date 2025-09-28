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
/* helper modified by LLM (iteration 5): fixed int literal comparisons and parameter types */
fn lemma_repeat_string_properties(s: Seq<char>, n: int)
    ensures
        n <= 0int ==> repeat_string_spec(s, n) == Seq::<char>::empty(),
        n == 1int ==> repeat_string_spec(s, n) == s,
        n == 0int ==> repeat_string_spec(s, n) == Seq::<char>::empty(),
        s == Seq::<char>::empty() ==> repeat_string_spec(s, n) == Seq::<char>::empty(),
    decreases (if n <= 0int { 0nat } else { n }) as nat
{
    if n <= 0int {
    } else if n == 1int {
    } else {
        lemma_repeat_string_properties(s, n - 1int);
    }
}

fn repeat_string(s: &String, n: i32) -> (result: String)
    requires n >= 0,
    ensures result@ == repeat_string_spec(s@, n as int),
{
    let mut result = String::new();
    let mut count = 0;
    
    while count < n
        invariant
            0 <= count <= n,
            result@ == repeat_string_spec(s@, count as int),
        decreases n - count
    {
        result = result + s;
        proof {
            lemma_repeat_string_properties(s@, count as int + 1int);
        }
        count = count + 1;
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
    /* code modified by LLM (iteration 5): fixed sequence indexing and type casting */
    let mut result: Vec<String> = Vec::new();
    let mut j = 0;
    
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            result.len() == j,
            forall|k: int| 0 <= k < j ==> 
                result[k]@ == repeat_string_spec(a[k]@, i[k] as int),
        decreases a.len() - j
    {
        let rep_string = if i[j] <= 0 {
            String::new()
        } else {
            repeat_string(&a[j], i[j])
        };
        
        proof {
            lemma_repeat_string_properties(a[j]@, i[j] as int);
        }
        
        result.push(rep_string);
        j = j + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}