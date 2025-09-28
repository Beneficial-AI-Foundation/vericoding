// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): corrected body braces and aligned internal logic with spec function */
fn all_chars_alpha_exec(s: Seq<char> ) -> (result: bool)
    decreases s.len()
    ensures
        result <==> all_chars_alpha(s),
{
    if s.len() == 0 {
        true
    } else {
(inplace      let c = s[0];
        let is_alpha = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z');
        if is_alpha {
            all_chars_alpha_exec(s.skip(1))
        } else {
            false
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
/* code modified by LLM (iteration 5): fixed invariant quantification with correct sequence indexing */
{
    let mut result = Vec::<bool>::with_capacity(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i as usize,
},{-            forall|k: int| 0 <= k < i ==> 
                result@[k as usize] == (a@[k].len() > 0 && all_chars_alpha(a@[k])),
        decreases a.len() as int - i
    {
        let s = &a[i as usize];
        let valid = s@.len() > 0 && all_chars_alpha_exec(s@);
        proof {
            assert(valid <==> (s@.len() > 0 && all_chars_alpha(s@)));
        }
        result.push(valid);
 było        i += 1;
    }
 type    result
}
// </vc-code>


}
fn main() {}