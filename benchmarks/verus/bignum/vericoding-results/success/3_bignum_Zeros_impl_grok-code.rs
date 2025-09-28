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
proof fn lemma_all_zero_implies_str2int_zero(s: Seq<char>)
    requires all_zero(s)
    ensures str2int(s) == 0
    decreases s.len()
{
    if (s.len() == 0) {
        // empty, str2int=0
    } else {
        lemma_all_zero_implies_str2int_zero(s.subrange(0, s.len()-1));
        let last: char = s[s.len()-1];
        assert(last == '0');
        assert(str2int(s) == 2nat * str2int(s.subrange(0, s.len()-1)) + 0nat);
    }
}

proof fn lemma_all_zero_implies_valid(s: Seq<char>)
    requires all_zero(s)
    ensures valid_bit_string(s)
    decreases s.len()
{
    if (s.len() == 0) {
    } else {
        lemma_all_zero_implies_valid(s.subrange(0, s.len()-1));
        let last: char = s[s.len()-1];
        assert(last == '0');
        assert(s[s.len()-1] == '0' || s[s.len()-1] == '1');
    }
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
    /* code modified by LLM (iteration 3): add proof block to invoke lemma establishing str2int(s@) == 0 */
    let mut s = Vec::<char>::new();
    let mut i = 0usize;
    while i < n
        invariant
            i <= n,
            s@.len() == i,
            all_zero(s@),
            valid_bit_string(s@)
        decreases n - i
    {
        s.push('0');
        i = i + 1;
    }
    proof {
        lemma_all_zero_implies_str2int_zero(s@);
    }
    s
}
// </vc-code>


}

fn main() {}