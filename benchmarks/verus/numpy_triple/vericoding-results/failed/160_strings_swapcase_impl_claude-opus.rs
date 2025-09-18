// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Make char_swapcase spec function with body instead of uninterpreted */
spec fn char_swapcase(c: char) -> char {
    if c >= 'a' && c <= 'z' {
        ((c as u8) - 32) as char
    } else if c >= 'A' && c <= 'Z' {
        ((c as u8) + 32) as char
    } else {
        c
    }
}

fn char_swapcase_impl(c: char) -> (swapped: char)
    ensures swapped == char_swapcase(c)
{
    if c >= 'a' && c <= 'z' {
        ((c as u8) - 32) as char
    } else if c >= 'A' && c <= 'Z' {
        ((c as u8) + 32) as char
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
/* code modified by LLM (iteration 5): Build new string character by character without String::new() */
{
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k]@.len() == a[k]@.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < a[k]@.len() ==> #[trigger] result[k]@[j] == char_swapcase(a[k]@[j])
    {
        let s = &a[i];
        let mut chars: Vec<char> = Vec::new();
        let mut j = 0;
        while j < s.len()
            invariant
                0 <= j <= s.len(),
                chars.len() == j,
                forall|k: int| 0 <= k < j ==> chars[k] == char_swapcase(s@[k])
        {
            let c = s.get_char(j);
            let swapped = char_swapcase_impl(c);
            chars.push(swapped);
            j = j + 1;
        }
        let new_s = String::from_vec(chars);
        result.push(new_s);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}