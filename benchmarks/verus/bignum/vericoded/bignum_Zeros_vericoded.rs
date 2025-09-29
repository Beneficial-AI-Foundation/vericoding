// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn all_zero(s: Seq<char>) -> bool {
    s.len() == 0 || forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma to prove str2int property when appending '0' */
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires valid_bit_string(s)
    ensures str2int(s.push('0')) == 2 * str2int(s)
{
    let extended = s.push('0');
    assert(extended.len() == s.len() + 1);
    assert(extended[extended.len() - 1] == '0');
    assert(extended.subrange(0, extended.len() - 1) =~= s);
}
// </vc-helpers>

// <vc-spec>
fn zeros(n: usize) -> (s: Vec<char>)
    ensures 
        s@.len() == n,
        valid_bit_string(s@),
        str2int(s@) == 0,
        all_zero(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added lemma call to maintain str2int invariant */
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result@.len() == i,
            valid_bit_string(result@),
            all_zero(result@),
            str2int(result@) == 0
        decreases n - i
    {
        proof {
            lemma_str2int_append_zero(result@);
            assert(str2int(result@) == 0);
            assert(2 * str2int(result@) == 0);
        }
        result.push('0');
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}