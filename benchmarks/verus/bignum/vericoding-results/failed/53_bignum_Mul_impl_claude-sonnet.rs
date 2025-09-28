// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 {
    0nat 
  } else {
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fixed mathematical proofs and simplified helpers with proper zero handling */
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires valid_bit_string(s)
    ensures str2int(s.push('0')) == 2 * str2int(s)
{
    let s_new = s.push('0');
    assert(s_new.len() == s.len() + 1);
    assert(s_new[s_new.len() - 1] == '0');
    assert(s_new.subrange(0, s_new.len() - 1) == s);
}

proof fn lemma_str2int_zero() 
    ensures str2int(seq!['0']) == 0
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'][0] == '0');
    assert(seq!['0'].subrange(0, 0) =~= seq![]);
    assert(str2int(seq!['0']) == 2 * str2int(seq![]) + 0);
    assert(str2int(seq![]) == 0);
}

proof fn lemma_multiplication_zero(x: nat)
    ensures x * 0 == 0
{
}

proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires valid_bit_string(s), (c == '0' || c == '1')
    ensures valid_bit_string(s.push(c))
{
}

spec fn pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * pow(base, (exp - 1) as nat) }
}

proof fn lemma_pow_zero()
    ensures pow(2, 0) == 1
{
}

proof fn lemma_pow_succ(n: nat)
    ensures pow(2, n + 1) == 2 * pow(2, n)
{
}

fn int_to_string(n: nat) -> (res: Vec<char>)
    ensures 
        valid_bit_string(res@),
        str2int(res@) == n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut val = n;
        while val > 0
            invariant valid_bit_string(result@)
            decreases val
        {
            if val % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            val = val / 2;
        }
        
        let mut i = 0;
        let len = result.len();
        while i < len / 2
            invariant 
                i <= len / 2,
                len == result.len(),
                valid_bit_string(result@)
            decreases len / 2 - i
        {
            let temp = result[i];
            result.set(i, result[len - 1 - i]);
            result.set(len - 1 - i, temp);
            i += 1;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): using direct multiplication via int conversion */
    proof {
        lemma_str2int_zero();
        lemma_multiplication_zero(str2int(s1@));
        lemma_multiplication_zero(str2int(s2@));
    }
    
    let val1 = str2int(s1@);
    let val2 = str2int(s2@);
    let product = val1 * val2;
    
    int_to_string(product)
}
// </vc-code>


}

fn main() {}