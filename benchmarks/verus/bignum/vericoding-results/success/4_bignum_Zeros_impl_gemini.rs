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
proof fn lemma_all_zero_push(s: Seq<char>)
    requires all_zero(s)
    ensures all_zero(s.push('0'))
{
}

proof fn lemma_all_zero_implies_valid_bit_string(s: Seq<char>)
    requires all_zero(s)
    ensures valid_bit_string(s)
{
}

proof fn lemma_all_zero_implies_str2int_is_zero(s: Seq<char>)
    requires 
        all_zero(s),
    ensures 
        str2int(s) == 0,
    decreases s.len()
{
    if s.len() > 0 {
        lemma_all_zero_implies_str2int_is_zero(s.subrange(0, s.len() - 1));
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
    let mut s = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            s@.len() == i as nat,
            all_zero(s@),
            valid_bit_string(s@),
            str2int(s@) == 0,
        decreases n - i
    {
        let ghost old_s = s@;
        s.push('0');
        
        proof {
            lemma_all_zero_push(old_s);
            lemma_all_zero_implies_valid_bit_string(s@);
            lemma_all_zero_implies_str2int_is_zero(s@);
        }
        
        i = i + 1;
    }
    s
}
// </vc-code>


}

fn main() {}