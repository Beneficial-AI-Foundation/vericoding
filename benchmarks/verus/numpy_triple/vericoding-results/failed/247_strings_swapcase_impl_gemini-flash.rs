// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed redundant char_swapcase spec definition. */
spec fn char_to_int(c: char)
{
    c as int
}

spec fn char_swapcase(c: char) -> char
{
    if 'a' <= c && c <= 'z' {
        (char_to_int(c) - char_to_int('a') + char_to_int('A')) as char
    } else if 'A' <= c && c <= 'Z' {
        (char_to_int(c) - char_to_int('A') + char_to_int('a')) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
spec fn char_swapcase(c: char) -> char;

spec fn string_swapcase(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::<char>::empty()
    } else {
        seq![char_swapcase(s[0])] + string_swapcase(s.skip(1))
    }
}

fn swapcase(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i]@.len() == a[i]@.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i]@.len() ==> 
            #[trigger] result[i]@[j] == char_swapcase(a[i]@[j])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Ensured correct handling of string views and indexing for verification. */
{
    let mut result: Vec<String> = Vec::new();
    let mut i: nat = 0;

    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k]@.len() == a[k]@.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < a[k]@.len() ==> result[k]@[j] == char_swapcase(a[k]@[j])
        decreases a.len() - i
    {
        let current_string = &a[i];
        let current_string_view = current_string.view();
        let mut swapped_string = String::new();
        let mut j: nat = 0;

        while j < current_string_view.len()
            invariant
                0 <= j,
                j <= current_string_view.len(),
                swapped_string.view().len() == j,
                forall|k: int| 0 <= k < j ==> swapped_string.view()[k] == char_swapcase(current_string_view[k])
            decreases current_string_view.len() - j
        {
            let original_char = current_string_view[j];
            let swapped_char = char_swapcase(original_char);
            swapped_string.push(swapped_char);
            j = j + 1;
        }
        result.push(swapped_string);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}