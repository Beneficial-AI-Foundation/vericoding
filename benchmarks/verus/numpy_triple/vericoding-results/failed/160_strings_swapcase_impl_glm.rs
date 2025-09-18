// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn char_swapcase(c: char) -> char {
    if c >= 'A' && c <= 'Z' {
        ((c as u8 + 32) as char)
    } else if c >= 'a' && c <= 'z' {
        ((c as u8 - 32) as char)
    } else {
        c
    }
}

fn exec_char_swapcase(c: char) -> (result: char)
    ensures result == char_swapcase(c)
{
    if c >= 'A' && c <= 'Z' {
        ((c as u8 + 32) as char)
    } else if c >= 'a' && c <= 'z' {
        ((c as u8 - 32) as char)
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
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k]@.len() == a[k]@.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < a[k]@.len() ==> 
                #[trigger] result[k]@[j] == char_swapcase(a[k]@[j])
    {
        let s = a[i];
        let mut new_s = String::new();
        let mut j = 0;
        for c in s.chars()
            invariant
                new_s@.len() == j,
                forall|k: int| 0 <= k < j ==> new_s@[k] == char_swapcase(s@[k])
        {
            let swapped = exec_char_swapcase(c);
            new_s.push(swapped);
            j = j + 1;
        }
        result.push(new_s);
    }
    result
}
// </vc-code>

}
fn main() {}