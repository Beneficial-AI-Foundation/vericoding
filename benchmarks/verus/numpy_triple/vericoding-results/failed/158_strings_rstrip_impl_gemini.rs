// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_whitespace_char(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

spec fn seq_contains(s: Seq<char>, c: char) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}

/* helper modified by LLM (iteration 5): fixed comma-separated invariant syntax */
fn string_contains(s: &String, c: char) -> (res: bool)
    ensures res == seq_contains(s@, c)
{
    let mut i: usize = 0;
    while i < s.len()
        decreases s.len() - i
        invariant i <= s.len()
        invariant forall |k:int| 0 <= k < i as int ==> s@[k] != c
    {
        vstd::string::lemma_string_char_at_is_substring_of_seq(s, i);
        if s.char_at(i) == c {
            return true;
        }
        i = i + 1;
    }
    return false;
}

/* helper modified by LLM (iteration 5): fixed trailing comma in invariant */
fn rstrip_string(s: &String, chars: &Option<String>) -> (res: String)
    ensures res@.len() <= s@.len()
{
    let mut work = s.clone();
    while work.len() > 0
        invariant work@.len() <= s@.len()
        decreases work.len()
    {
        vstd::string::lemma_pop_is_drop_last(&work);
        let c = work.pop().unwrap();

        let strip = match chars {
            Some(strip_s) => string_contains(strip_s, c),
            None => is_whitespace_char(c),
        };

        if !strip {
            vstd::string::lemma_push_is_add(&mut work, c);
            work.push(c);
            break;
        }
    }
    work
}
// </vc-helpers>

// <vc-spec>
fn rstrip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() <= a[i]@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed comma-separated invariant syntax */
{
    let mut result: Vec<String> = Vec::new();
    let mut i: int = 0;
    while i < a.len() as int
        invariant 0 <= i <= a.len() as int
        invariant result.len() == i as nat
        invariant forall|j: int| 0 <= j < i ==> #[trigger] result@[j]@.len() <= a@[j]@.len()
        decreases a.len() as int - i
    {
        let s = &a[i as usize];
        let stripped_s = rstrip_string(s, &chars);
        result.push(stripped_s);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}