// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn rstrip_string_spec(s: &Seq<char>, chars: &Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let last_idx = (s.len() - 1) as int;
        let last_char = s[last_idx];
        if chars.contains(last_char) {
            rstrip_string_spec(&s.subrange(0, last_idx as int), chars)
        } else {
            *s
        }
    }
}

spec fn rstrip_whitespace_spec(s: &Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let last_idx = (s.len() - 1) as int;
        let last_char = s[last_idx];
        if last_char.is_ascii_whitespace() {
            rstrip_whitespace_spec(&s.subrange(0, last_idx as int))
        } else {
            *s
        }
    }
}

/* helper modified by LLM (iteration 5): Fixed &mut parameter issue by using indexing instead of chars().nth() */
fn rstrip_single(s: &String, chars: &Option<String>) -> (result: String)
    ensures
        result@.len() <= s@.len(),
        match chars {
            Some(c) => result@ == rstrip_string_spec(&s@, &c@),
            None => result@ == rstrip_whitespace_spec(&s@),
        }
{
    let mut i = s.len();
    match chars {
        Some(c) => {
            while i > 0
                invariant
                    0 <= i,
                    i <= s@.len(),
                    forall|j: int| i <= j < s@.len() ==> c@.contains(#[trigger] s@[j]),
            {
                let prev = i - 1;
                let ch = s@[prev as int];
                if !c@.contains(ch) {
                    break;
                }
                i = i - 1;
            }
        },
        None => {
            while i > 0
                invariant
                    0 <= i,
                    i <= s@.len(),
                    forall|j: int| i <= j < s@.len() ==> (#[trigger] s@[j]).is_ascii_whitespace(),
            {
                let prev = i - 1;
                let ch = s@[prev as int];
                if !ch.is_ascii_whitespace() {
                    break;
                }
                i = i - 1;
            }
        }
    }
    String::from(&s@.subrange(0, i as int))
}
// </vc-helpers>

// <vc-spec>
fn rstrip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() <= a[i]@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implementation remains the same as iteration 4 */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j]@.len() <= a[j]@.len(),
    {
        let stripped = rstrip_single(&a[i], &chars);
        result.push(stripped);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}