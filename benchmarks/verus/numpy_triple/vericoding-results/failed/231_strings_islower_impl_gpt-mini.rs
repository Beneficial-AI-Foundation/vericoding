// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): iterative check for any alphabetic char in seq */
fn seq_has_alpha(s: Seq<char>) -> (result: bool)
    ensures
        result == string_has_cased_char(s),
    decreases s.len()
{
    let mut i: nat = 0;
    let n: nat = s.len();
    let mut found: bool = false;
    while i < n
        invariant
            i <= n,
            found ==> exists|j: int| 0 <= j < i as int && is_alpha_char(s[j]),
            !found ==> forall|j: int| 0 <= j < i as int ==> !is_alpha_char(s[j]),
        decreases n - i
    {
        let c: char = s.index(i);
        if is_alpha_char(c) {
            found = true;
        }
        i = i + 1;
    }
    found
}

/* helper modified by LLM (iteration 5): iterative check that all alphabetic chars are lowercase */
fn seq_all_cased_lower(s: Seq<char>) -> (result: bool)
    ensures
        result == string_all_cased_are_lowercase(s),
    decreases s.len()
{
    let mut i: nat = 0;
    let n: nat = s.len();
    let mut ok: bool = true;
    while i < n
        invariant
            i <= n,
            ok ==> forall|j: int| 0 <= j < i as int ==> (!is_alpha_char(s[j]) || is_lower_char(s[j])),
            !ok ==> exists|j: int| 0 <= j < i as int && is_alpha_char(s[j]) && !is_lower_char(s[j]),
        decreases n - i
    {
        let c: char = s.index(i);
        if is_alpha_char(c) {
            if !is_lower_char(c) {
                ok = false;
            }
        }
        i = i + 1;
    }
    ok
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

spec fn is_lower_char(c: char) -> bool {
    'a' <= c <= 'z'
}

spec fn string_has_cased_char(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_alpha_char(s[i])
}

spec fn string_all_cased_are_lowercase(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() && is_alpha_char(s[i]) ==> is_lower_char(s[i])
}

fn islower(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i as int] == (string_has_cased_char(a[i]@) && string_all_cased_are_lowercase(a[i]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over input strings and apply seq helpers */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    let n: usize = a.len();
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < result.len() as int ==> result[j as int] == (string_has_cased_char(a[j as usize]@) && string_all_cased_are_lowercase(a[j as usize]@)),
        decreases n - i
    {
        let sseq: Seq<char> = a[i]@;
        let b: bool = seq_has_alpha(sseq) && seq_all_cased_lower(sseq);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}