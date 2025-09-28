// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): head char is decimal when all_chars_decimal and non-empty */
proof fn helper_all_chars_head(s: Seq<char>)
    requires
        all_chars_decimal(s),
        s.len() > 0,
    ensures
        is_decimal_char(s@[0]),
{
    if s.len() == 0 {
    } else {
        // by definition of all_chars_decimal on non-empty sequence
        assert(is_decimal_char(s@[0]));
    }
}

// </vc-helpers>

// <vc-spec>
spec fn is_decimal_char(c: char) -> bool {
    ('0' <= c && c <= '9')
}

spec fn all_chars_decimal(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_decimal_char(s[0]) && all_chars_decimal(s.skip(1))
    }
}

fn isdecimal(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& (result[i] == true <==> (a[i]@.len() > 0 && all_chars_decimal(a[i]@)))
            &&& (a[i]@ == Seq::<char>::empty() ==> result[i] == false)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over Vec<String> using int indices and @ indexing for Vec/Seq */
    let n: int = a.len() as int;
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            result.len() as int == i,
            forall|j: int| 0 <= j < result.len() as int ==> (result@[j] == true <==> (a@[j]@.len() > 0 && all_chars_decimal(a@[j]@))),
        decreases n - i
    {
        let sseq: Seq<char> = a@[i]@;
        let mut ok: bool = true;
        if sseq.len() == 0 {
            ok = false;
        } else {
            let m: int = sseq.len() as int;
            let mut k: int = 0;
            while k < m
                invariant
                    0 <= k <= m,
                    ok ==> forall|t: int| 0 <= t < k ==> is_decimal_char(sseq@[t]),
                decreases m - k
            {
                if !is_decimal_char(sseq@[k]) {
                    ok = false;
                }
                k = k + 1;
            }
        }
        result.push(ok);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}