// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn char_swapcase(c: char) -> char {
    if 'a' <= c && c <= 'z' {
        ((c as u32 - 'a' as u32) + 'A' as u32) as char
    } else if 'A' <= c && c <= 'Z' {
        ((c as u32 - 'A' as u32) + 'a' as u32) as char
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
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant result@.len() == i,
                  forall |k: int| 0 <= k < i ==> result@[k] == string_swapcase(a@[k])
    {
        let original = a@[i];
        let mut swapped_chars = Vec::new();
        let mut j = 0;
        while j < original.len()
            invariant swapped_chars@.len() == j,
                      forall |l: int| 0 <= l < j ==> swapped_chars@[l] == char_swapcase(original@[l])
        {
            swapped_chars.push(char_swapcase(original@[j]));
            j += 1;
        }
        result.push(swapped_chars@);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}