// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix spec function and convert chars to string helper */
spec fn char_swapcase(c: char) -> char;

fn convert_chars_to_string(chars: Vec<char>) -> (s: String)
    ensures s@.len() == chars.len(),
            forall|i: int| 0 <= i < chars.len() ==> s@[i] == chars[i]
{
    let mut result = String::new();
    let mut i = 0;
    while i < chars.len()
        invariant
            i <= chars.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == chars[j]
    {
        result.push(chars[i]);
        i += 1;
    }
    result
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
    /* code modified by LLM (iteration 5): fix type mismatches and indexing */
    let mut result = Vec::<String>::new();
    let mut k = 0;
    while k < a.len()
        invariant
            result.len() == k,
            k <= a.len(),
            forall|i: int| 0 <= i < k ==> result[i]@.len() == a[i]@.len(),
            forall|i: int, j: int| 0 <= i < k && 0 <= j < a[i]@.len() ==> 
                result[i]@[j] == char_swapcase(a[i]@[j])
    {
        let mut chars = Vec::<char>::new();
        let mut m = 0;
        while m < a[k as int]@.len()
            invariant
                chars.len() == m,
                m <= a[k as int]@.len(),
                forall|j: int| 0 <= j < m ==> chars[j] == char_swapcase(a[k as int]@[j])
        {
            chars.push(char_swapcase(a[k as int]@[m]));
            m += 1;
        }
        let swapped_string = convert_chars_to_string(chars);
        result.push(swapped_string);
        k += 1;
    }
    result
}
// </vc-code>

}
fn main() {}