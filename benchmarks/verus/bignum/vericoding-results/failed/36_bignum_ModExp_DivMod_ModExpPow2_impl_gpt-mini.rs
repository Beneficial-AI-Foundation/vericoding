// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
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
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2int(divisor) > 0
  ensures 
    ({
       let (quotient, remainder) = result; 
       valid_bit_string(quotient) && valid_bit_string(remainder) &&
       str2int(quotient) == str2int(dividend) / str2int(divisor) &&
       str2int(remainder) == str2int(dividend) % str2int(divisor)
    })
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
    (str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0) &&
    sy.len() == n + 1 &&
    str2int(sz) > 1
  ensures 
    valid_bit_string(res) &&
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): spec nat_to_bitseq without requires */
spec fn nat_to_bitseq(x: nat, len: int) -> Seq<char>
  decreases len
{
    if len == 0 { Seq::empty() } else { let prefix = nat_to_bitseq(x / 2nat, len - 1); prefix + seq![if x % 2nat == 1nat { '1' } else { '0' }] }
}

/* helper modified by LLM (iteration 10): spec view of Vec */
spec fn seq_of_vec(v: Vec<char>) -> Seq<char> {
    v@
}

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): compute modular exponentiation using runtime u128 and build result Vec<char> */
{
  // convert sx (bits, MSB at index 0) to runtime integer
  let mut bx: u128 = 0u128;
  let mut i: usize = 0usize;
  while i < sx.len() {
      let c = sx[i];
      if c == '1' { bx = bx * 2u128 + 1u128; } else { bx = bx * 2u128; }
      i += 1;
  }

  // convert sy to runtime integer
  let mut be: u128 = 0u128;
  let mut j: usize = 0usize;
  while j < sy.len() {
      let c = sy[j];
      if c == '1' { be = be * 2u128 + 1u128; } else { be = be * 2u128; }
      j += 1;
  }

  // convert sz to runtime integer (modulus)
  let mut bm: u128 = 0u128;
  let mut k: usize = 0usize;
  while k < sz.len() {
      let c = sz[k];
      if c == '1' { bm = bm * 2u128 + 1u128; } else { bm = bm * 2u128; }
      k += 1;
  }

  // compute modular exponentiation (base^exp mod m)
  let mut resnum: u128 = 0u128;
  if bm == 0u128 {
      // undefined modulus; produce zero vector of appropriate length
      resnum = 0u128;
  } else {
      let mut base = bx % bm;
      let mut exp = be;
      let mut acc: u128 = 1u128 % bm;
      while exp > 0u128 {
          if (exp & 1u128) == 1u128 {
              acc = (acc * base) % bm;
          }
          exp = exp >> 1u128;
          base = (base * base) % bm;
      }
      resnum = acc;
  }

  // build result Vec<char> of length sz.len(), MSB at index 0
  let mut out: Vec<char> = Vec::new();
  let len = sz.len();
  let mut idx: usize = 0usize;
  while idx < len {
      // bit position: index 0 = most significant, index (len-1) = least significant
      let shift = (len - 1 - idx) as u32;
      let bit = if shift < 128u32 { ((resnum >> shift) & 1u128) == 1u128 } else { false };
      if bit { out.push('1'); } else { out.push('0'); }
      idx += 1;
  }
  out
}

// </vc-code>


}

fn main() {}