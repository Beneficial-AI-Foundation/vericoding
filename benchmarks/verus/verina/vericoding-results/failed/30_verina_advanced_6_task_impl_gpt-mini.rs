// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn to_lower(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as int + 32) as char)
    } else {
        c
    }
}

spec fn normalize_str(s: &str) -> Seq<char> {
    s.view().map_values(|c| to_lower(c))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove ASCII lowercasing view equals normalize_str */
proof fn to_ascii_lower_view_eq_normalize(s: &str)
    ensures s.to_ascii_lowercase().view() == normalize_str(s)
{
    let orig = s.view();
    let lower = s.to_ascii_lowercase().view();
    assert(orig.len() == lower.len());
    let mut i: int = 0;
    while i < orig.len()
        invariant 0 <= i && i <= orig.len(),
        decreases orig.len() - i
    {
        proof {
            let oc = orig.index(i);
            let lc = lower.index(i);
            if 'A' <= oc && oc <= 'Z' {
                assert(lc == ((oc as int + 32) as char));
            } else {
                assert(lc == oc);
            }
        }
        i = i + 1;
    }
    assert(lower == normalize_str(s));
}

// </vc-helpers>

// <vc-spec>
fn all_vowels(s: &str) -> (result: bool)
    ensures
        result <==> (
            normalize_str(s).contains('a') &&
            normalize_str(s).contains('e') &&
            normalize_str(s).contains('i') &&
            normalize_str(s).contains('o') &&
            normalize_str(s).contains('u')
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): relate normalized spec to runtime lowercasing and check vowels */
    let lower = s.to_ascii_lowercase();
    let mut fa = false;
    let mut fe = false;
    let mut fi = false;
    let mut fo = false;
    let mut fu = false;

    for ch in lower.chars() {
        if ch == 'a' { fa = true; }
        if ch == 'e' { fe = true; }
        if ch == 'i' { fi = true; }
        if ch == 'o' { fo = true; }
        if ch == 'u' { fu = true; }
        if fa && fe && fi && fo && fu { break; }
    }

    let result = fa && fe && fi && fo && fu;
    proof { to_ascii_lower_view_eq_normalize(s); }
    result
}

// </vc-code>

}
fn main() {}