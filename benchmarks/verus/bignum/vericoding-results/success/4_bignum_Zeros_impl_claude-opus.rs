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
/* helper modified by LLM (iteration 3): added lemma to prove str2int remains 0 when appending '0' */
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires
        valid_bit_string(s),
        str2int(s) == 0,
    ensures
        str2int(s.push('0')) == 0,
{
    let s_new = s.push('0');
    assert(s_new.len() == s.len() + 1);
    assert(s_new[s_new.len() - 1] == '0');
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
    assert(str2int(s_new) == 2 * str2int(s) + 0);
    assert(str2int(s_new) == 2 * 0 + 0);
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
    let mut s = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            s@.len() == i,
            valid_bit_string(s@),
            all_zero(s@),
            str2int(s@) == 0,
        decreases n - i
    {
        proof {
            lemma_str2int_append_zero(s@);
        }
        s.push('0');
        i = i + 1;
    }
    s
}
// </vc-code>


}

fn main() {}