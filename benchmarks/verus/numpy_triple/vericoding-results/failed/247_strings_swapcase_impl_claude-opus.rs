// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate char_swapcase declaration */
proof fn string_swapcase_len(s: Seq<char>)
    ensures
        string_swapcase(s).len() == s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        string_swapcase_len(s.skip(1));
    }
}

fn swapcase_char(c: char) -> (result: char)
    ensures
        result == char_swapcase(c)
{
    if c >= 'a' && c <= 'z' {
        ((c as u8) - ('a' as u8) + ('A' as u8)) as char
    } else if c >= 'A' && c <= 'Z' {
        ((c as u8) - ('A' as u8) + ('a' as u8)) as char
    } else {
        c
    }
}

fn swapcase_string(s: &String) -> (result: String)
    ensures
        result@.len() == s@.len(),
        forall|j: int| 0 <= j < s@.len() ==> result@[j] == char_swapcase(s@[j])
{
    let mut chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.unicode_len()
        invariant
            i <= s@.len(),
            chars@.len() == i as int,
            forall|j: int| 0 <= j < i ==> chars@[j] == char_swapcase(s@[j])
    {
        let c = s.get_char(i);
        let swapped = swapcase_char(c);
        chars.push(swapped);
        i = i + 1;
    }
    
    String::from_rust_string(chars.into_iter().collect::<std::string::String>())
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
    /* code modified by LLM (iteration 5): Main implementation calling helper function */
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j]@.len() == a[j]@.len(),
            forall|j: int, k: int| 0 <= j < i && 0 <= k < a[j]@.len() ==> 
                #[trigger] result[j]@[k] == char_swapcase(a[j]@[k])
    {
        let swapped = swapcase_string(&a[i]);
        result.push(swapped);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}