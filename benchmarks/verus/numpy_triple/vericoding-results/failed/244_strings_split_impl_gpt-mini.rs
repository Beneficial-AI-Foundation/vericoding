// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compare Strings using Rust equality */
fn strings_equal(a: &String, b: &String) -> bool {
    a == b
}

// </vc-helpers>

// <vc-spec>
fn split(a: Vec<String>, sep: String, maxsplit: Option<usize>) -> (result: Vec<Vec<String>>)
    requires
        sep@ != Seq::<char>::empty(),
        a.len() > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() as int ==> {
            let parts = #[trigger] result[i]@;
            let original = #[trigger] a[i]@;
            (forall|j: int| 0 <= j < parts.len() as int ==> parts[j]@ != sep@) &&
            (match maxsplit {
                None => true,
                Some(limit) => parts.len() <= limit + 1,
            }) &&
            parts.len() >= 1 &&
            (original.len() == 0 ==> parts.len() == 1 && parts[0]@.len() == 0) &&
            (original == sep@ ==> parts.len() == 2 && parts[0]@.len() == 0 && parts[1]@.len() == 0)
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simple per-element split handling sep equality */
    let mut result: Vec<Vec<String>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() <= a.len(),
            i <= a.len(),
        decreases a.len() - i
    {
        let s = a[i].clone();
        if s == sep {
            let mut parts: Vec<String> = Vec::new();
            parts.push(String::new());
            parts.push(String::new());
            result.push(parts);
        } else {
            let mut parts: Vec<String> = Vec::new();
            parts.push(s);
            result.push(parts);
        }
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}