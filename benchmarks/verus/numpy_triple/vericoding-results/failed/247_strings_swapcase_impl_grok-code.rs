// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed duplicate char_swapcase declaration and erroneous ensures on spec fns */
spec fn is_lower(c: char) -> bool {
    'a' <= c && c <= 'z'
}

spec fn is_upper(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

spec fn to_upper(c: char) -> char {
    ((c as int - 'a' as int) + 'A' as int) as char
}

spec fn to_lower(c: char) -> char {
    ((c as int - 'A' as int) + 'a' as int) as char
}

spec fn char_swapcase(c: char) -> char {
    if is_lower(c) { to_upper(c) } else if is_upper(c) { to_lower(c) } else { c }
}

fn char_swapcase_exec(c: char) -> (r: char)
    ensures
        r == char_swapcase(c),
{
    if c >= 'a' && c <= 'z' {
        ((c as i32 - 'a' as i32) + 'A' as i32) as char
    } else if c >= 'A' && c <= 'Z' {
        ((c as i32 - 'A' as i32) + 'a' as i32) as char
    } else {
        c
    }
}

/* helper modified by LLM (iteration 3): fixed invariant syntax error */
fn swapcase_string(s: &String) -> (result: String)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> result@[i] == char_swapcase(s@[i])
{
    let mut v: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == char_swapcase(s@[j])
        decreases s.len() - i
    {
        v.push(char_swapcase_exec(s[i]));
        i += 1;
    }
    String::from(v)
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
/* code modified by LLM (iteration 3): added required comment */
{
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j]@.len() == a[j]@.len(),
            forall|j: int, k: int| 0 <= j < i && 0 <= k < a[j]@.len() ==> 
                #[trigger] result[j]@[k] == char_swapcase(a[j]@[k])
        decreases a.len() - i
    {
        let swapped = swapcase_string(&a[i]);
        result.push(swapped);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}