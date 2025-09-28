// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma about head character when all_chars_alpha holds on a nonempty sequence */
proof fn lemma_all_chars_alpha_head(s: Seq<char>)
    ensures
        s.len() == 0 ==> all_chars_alpha(s),
        s.len() > 0 && all_chars_alpha(s) ==> is_alpha_char(s[0]),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        if all_chars_alpha(s) {
            assert(is_alpha_char(s[0]) && all_chars_alpha(s.skip(1)));
        }
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

spec fn all_chars_alpha(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alpha_char(s[0]) && all_chars_alpha(s.skip(1))
    }
}

fn isalpha(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i as int] == (a[i as int]@.len() > 0 && all_chars_alpha(a[i as int]@)),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() == 0 ==> result[i as int] == false),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() > 0 ==> (result[i as int] <==> all_chars_alpha(a[i as int]@))),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> a[i as int]@.len() > 0),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> all_chars_alpha(a[i as int]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid using int/spec len in exec, use usize len and spec predicate only */
    let n = a.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(),
            i as int <= a.len() as int,
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> res[j as int] == (a[j as int]@.len() > 0 && all_chars_alpha(a[j as int]@)),
        decreases (n as int) - (i as int)
    {
        let b: bool = (a[i].len() > 0) && all_chars_alpha(a[i]@);
        res.push(b);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}