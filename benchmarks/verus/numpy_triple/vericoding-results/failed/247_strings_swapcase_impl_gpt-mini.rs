// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert Seq<char> to String preserving spec */
fn string_from_seq(s: Seq<char>) -> (result: String)
    ensures
        result@ == s,
{
    let mut t = String::new();
    let mut i: nat = 0;
    while i < s.len()
        invariant
            t@ == s[..i],
        decreases s.len() - i
    {
        t.push_char(s[i]);
        i += 1;
    }
    result = t;
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
    /* code modified by LLM (iteration 5): build result vector by converting each input string via spec swapcase */
    let mut result: Vec<String> = Vec::new();
    let mut i: int = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k]@ == string_swapcase(a[k]@),
        decreases a.len() - i
    {
        let s_spec: Seq<char> = a[i]@;
        let t: String = string_from_seq(string_swapcase(s_spec));
        result.push(t);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}