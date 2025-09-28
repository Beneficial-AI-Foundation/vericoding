// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_alphanumeric(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')
}

spec fn to_lowercase(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u32) + 32) as char
    } else {
        c
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): improved annotations and ASCII conversion safety */
fn is_alphanumeric_exec(c: char) -> (res: bool)
    ensures
        res == is_alphanumeric(c)
{
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')
}

/* helper modified by LLM (iteration 5): use u8-based ASCII conversion with spec refinement */
fn to_lowercase_exec(c: char) -> (res: char)
    ensures
        res == to_lowercase(c)
{
    if 'A' <= c && c <= 'Z' {
        let lower_u8 = (c as u8) + 32u8;
        lower_u8 as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn palindrome_ignore_non_alnum(s: &str) -> (result: bool)
    ensures 
        result <==> ({
            let chars_seq = s@;
            let cleaned = chars_seq.filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c));
            let forward = cleaned;
            let backward = cleaned.reverse();
            forward == backward
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build cleaned vector with invariants; then build reverse and compare */
    let mut filtered: Vec<char> = Vec::new();

    let mut it = s.chars();
    let n: usize = s.chars().count();
    let mut t: usize = 0;
    while t < n
        invariant
            t <= n,
            n as int == s@.len(),
            filtered@ == s@.subrange(0, t).filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c)),
        decreases (n - t) as int
    {
        let ch = it.next().unwrap();
        if is_alphanumeric_exec(ch) {
            filtered.push(to_lowercase_exec(ch));
        }
        t += 1;
    }

    let m: usize = filtered.len();
    let mut backward: Vec<char> = Vec::new();
    let mut k: usize = m;
    while k > 0
        invariant
            k <= m,
            backward@ == filtered@.subrange(k, m).reverse(),
        decreases k as int
    {
        k -= 1;
        backward.push(filtered[k]);
    }

    let is_pal: bool = filtered == backward;

    proof {
        assert(filtered@ == s@.filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c)));
        assert(backward@ == filtered@.reverse());
    }

    is_pal
}
// </vc-code>

}
fn main() {}