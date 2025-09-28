// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Added pow2nat spec function and fixed lemma_str2int_append */
spec fn pow2nat(n: nat) -> nat {
    if n == 0 { 1nat } else { 2nat * pow2nat(n - 1) }
}

proof fn lemma_str2int_append(s: Seq<char>, c: char)
  requires
    valid_bit_string(s),
    c == '0' || c == '1'
  ensures
    str2int(s.push(c)) == 2int * str2int(s) + (if c == '1' { 1int } else { 0int })
decreases s.len()
{
  if s.len() == 0 {
    assert(str2int(Seq::new(0, |i| c)) == (if c == '1' { 1nat } else { 0nat }));
  } else {
    lemma_str2int_append(s.subrange(0, s.len() - 1), s[s.len() - 1]);
    let s_sub = s.push(c).subrange(0, s.len());
    assert(s_sub =~= s);
    lemma_str2int_append(s_sub, c);
  }
}

fn add(a: Vec<char>, b: Vec<char>) -> (result: Vec<char>)
  requires
    valid_bit_string(a@) && valid_bit_string(b@)
  ensures
    valid_bit_string(result@),
    str2int(result@) == str2int(a@) + str2int(b@)
{
    let mut res = Vec::new();
    let mut carry = 0;
    let mut i = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    while i < max_len || carry != 0
        invariant
            i <= max_len + 1,
            valid_bit_string(res@),
            str2int(res@) + carry as int * pow2nat(i as nat) == 
                str2int(a@.subrange((a.len() as int) - i, a.len() as int)) + 
                str2int(b@.subrange((b.len() as int) - i, b.len() as int))
        decreases (max_len - i) as int
    {
        let a_bit = if i < a.len() { a[a.len() - 1 - i] == '1' } else { false };
        let b_bit = if i < b.len() { b[b.len() - 1 - i] == '1' } else { false };
        
        let sum = (a_bit as u8) + (b_bit as u8) + carry;
        let new_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        res.push(new_bit);
        i += 1;
    }
    
    res.reverse();
    if res.is_empty() { vec!['0'] } else { res }
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed multiplication algorithm with proper invariants */
{
    if s1.is_empty() || s2.is_empty() {
        return vec!['0'];
    }
    
    let mut res = vec!['0'];
    let mut temp = s2.clone();
    let mut shift = 0;
    
    while !temp.is_empty()
        invariant
            valid_bit_string(res@),
            valid_bit_string(temp@),
            str2int(res@) == str2int(s1@) * (str2int(s2@) - str2int(temp@) * pow2nat(shift as nat)),
            res@.len() >= 1,
            temp@.len() <= s2@.len()
        decreases temp@.len()
    {
        let last_char = temp.last().unwrap();
        temp.pop();
        
        if *last_char == '1' {
            let mut shifted_s1 = s1.clone();
            for _ in 0..shift {
                shifted_s1.push('0');
            }
            res = add(res, shifted_s1);
        }
        
        shift += 1;
    }
    
    res
}
// </vc-code>


}

fn main() {}