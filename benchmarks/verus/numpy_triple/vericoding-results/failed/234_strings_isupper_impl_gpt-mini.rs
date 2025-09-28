// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): mark is_alpha_char as uninterpreted */
spec fn is_alpha_char(c: char) -> bool { uninterp }

/* helper modified by LLM (iteration 5): mark is_upper_char as uninterpreted */
spec fn is_upper_char(c: char) -> bool { uninterp }

/* helper modified by LLM (iteration 5): trivial proof that sequence length is non-negative */
proof fn seq_len_nonneg(s: Seq<char>)
    ensures
        s.len() >= 0,
{
    assert(s.len() >= 0);
}

// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool;

spec fn is_upper_char(c: char) -> bool;

spec fn has_alpha_chars(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_alpha_char(s[i])
}

spec fn all_alpha_are_upper(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() && is_alpha_char(s[i]) ==> is_upper_char(s[i])
}

fn isupper(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i] == {
            let s = a[i]@;
            s.len() > 0 && has_alpha_chars(s) && all_alpha_are_upper(s)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute isupper for each string */
    let mut res = Vec::<bool>::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
        decreases a.len() - i
    {
        let s: Seq<char> = a[i]@;
        let b: bool = s.len() > 0 && has_alpha_chars(s) && all_alpha_are_upper(s);
        res.push(b);
        i = i + 1;
    }
    let result = res;
    result
}
// </vc-code>


}
fn main() {}