// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn exec_string_ends_with(a: &String, suffix: &String) -> (result: bool)
    ensures
        result == string_ends_with(a@, suffix@)
{
    /* helper modified by LLM (iteration 5): Fixed type mismatches by using int for lengths and counters */
    let a_char_count: int = a@.len();
    let suffix_char_count: int = suffix@.len();
    if suffix_char_count > a_char_count {
        return false;
    }
    let mut a_iter = a.chars();
    let mut counter: int = 0;
    while counter < a_char_count - suffix_char_count
        invariant counter <= a_char_count - suffix_char_count,
        decreases (a_char_count - suffix_char_count) - counter
    {
        let _ = a_iter.next();
        counter += 1;
    }
    let mut suffix_iter = suffix.chars();
    let mut j: int = 0;
    while j < suffix_char_count
        invariant j <= suffix_char_count,
        decreases suffix_char_count - j
    {
        let a_char = a_iter.next().unwrap();
        let s_char = suffix_iter.next().unwrap();
        if a_char != s_char {
            return false;
        }
        j += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
spec fn string_ends_with(s: Seq<char>, suffix: Seq<char>) -> bool {
    if suffix.len() > s.len() {
        false
    } else {
        s.subrange(s.len() - suffix.len(), s.len() as int) == suffix
    }
}

fn endswith(a: Vec<String>, suffix: Vec<String>) -> (result: Vec<bool>)
    requires a.len() == suffix.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            /* Main specification: result matches string_ends_with for each pair */
            result[i] == string_ends_with(a[i]@, suffix[i]@) &&
            /* Mathematical property: if result is true, suffix appears at the end */
            (result[i] ==> {
                suffix[i]@.len() <= a[i]@.len() &&
                a[i]@.subrange(a[i]@.len() - suffix[i]@.len(), a[i]@.len() as int) == suffix[i]@
            }) &&
            /* Mathematical property: if result is false, suffix does not appear at the end */
            (!result[i] ==> {
                suffix[i]@.len() > a[i]@.len() ||
                a[i]@.subrange(a[i]@.len() - suffix[i]@.len(), a[i]@.len() as int) != suffix[i]@
            })
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed, compilation error was in helpers */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result@[j] == string_ends_with(a[j]@, suffix[j]@)
        decreases a.len() - i
    {
        result.push(exec_string_ends_with(&a[i], &suffix[i]));
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}