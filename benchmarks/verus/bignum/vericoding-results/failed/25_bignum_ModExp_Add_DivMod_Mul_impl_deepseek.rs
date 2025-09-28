// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2int(divisor) > 0,
  ensures 
    valid_bit_string(ret.0) && valid_bit_string(ret.1) &&
    str2int(ret.0) == str2int(dividend) / str2int(divisor) &&
    str2int(ret.1) == str2int(dividend) % str2int(divisor),
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) * str2int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type conversions and cleaned up ghost type usage */
fn vec_to_seq(v: Vec<char>) -> Seq<char> { v@ }
fn seq_to_vec(s: Seq<char>) -> Vec<char> {
    let len: usize = s.len() as usize;
    let mut v = Vec::with_capacity(len);
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            v@.len() == i as nat,
            forall|j: int| 0 <= j < i ==> v[j] == s[j as int],
    {
        let c: char = s[i as int];
        v.push(c);
        i += 1;
    }
    v
}
proof fn lemma_str2int_div_mod(dividend: Seq<char>, divisor: Seq<char>)
    requires
        valid_bit_string(dividend) && valid_bit_string(divisor),
        str2int(divisor) > 0,
    ensures
        str2int(dividend) == str2int(divisor) * (str2int(dividend) / str2int(divisor)) + str2int(dividend) % str2int(divisor),
{
    // Div/mod lemma for specification
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed type errors with subrange and length comparisons */
{
    let sy_seq = sy@;
    if sy_seq.len() == 0nat {
        let one: Seq<char> = seq!['1'];
        seq_to_vec(one)
    } else if sy_seq.len() == 1nat {
        if sy_seq[0 as int] == '1' {
            let (_, remainder) = div_mod(sx@, sz@);
            seq_to_vec(remainder)
        } else {
            let one: Seq<char> = seq!['1'];
            seq_to_vec(one)
        }
    } else {
        let half_len: int = (sy_seq.len() as int) / 2;
        let q = sy_seq.subrange(0 as int, half_len);
        let half = mod_exp(sx.clone(), seq_to_vec(q), sz.clone());
        let temp = mul(half@, half@);
        let (_, r2) = div_mod(temp, sz@);
        let remaining = sy_seq.subrange(half_len, sy_seq.len() as int);
        let should_multiply = remaining.len() > 0nat && remaining[0 as int] == '1';
        if should_multiply {
            let temp2 = mul(r2, sx@);
            let (_, r3) = div_mod(temp2, sz@);
            seq_to_vec(r3)
        } else {
            seq_to_vec(r2)
        }
    }
}
// </vc-code>


}

fn main() {}