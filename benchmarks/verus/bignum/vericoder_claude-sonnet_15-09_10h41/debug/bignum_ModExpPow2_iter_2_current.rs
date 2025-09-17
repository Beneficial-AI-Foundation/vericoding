use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
    decreases y 
  {
    if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
  }
  
spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed type casting in vec_from_seq by using usize indexing */
spec fn pow_mod(base: nat, exp: nat, modulus: nat) -> nat
{
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let half_pow = pow_mod(base, exp / 2, modulus);
        (half_pow * half_pow) % modulus
    } else {
        (base * pow_mod(base, exp - 1, modulus)) % modulus
    }
}

spec fn nat_to_bit_string(n: nat, len: nat) -> Seq<char>
{
    if len == 0 {
        seq![]
    } else {
        let bit = if n % 2 == 1 { '1' } else { '0' };
        nat_to_bit_string(n / 2, len - 1).push(bit)
    }
}

exec fn vec_from_seq(s: Seq<char>) -> (res: Vec<char>)
    ensures res@ == s
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@ == s.subrange(0, i as int)
    {
        v.push(s[i]);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type casting issues by using usize */
    if n == 0 {
        if sx@.len() > 0 && sx@[0] == '0' {
            return vec_from_seq(seq!['1']);
        } else {
            let base_mod = Str2Int(sx@) % Str2Int(sz@);
            return vec_from_seq(nat_to_bit_string(base_mod, 1));
        }
    }
    
    let sy_int = Str2Int(sy@);
    if sy_int == 0 {
        return vec_from_seq(seq!['1']);
    }
    
    let sx_int = Str2Int(sx@);
    let sz_int = Str2Int(sz@);
    
    if sy_int % 2 == 0 {
        let half_exp = sy_int / 2;
        let sy_half = nat_to_bit_string(half_exp, n as usize);
        let temp_result = ModExpPow2(sx, &vec_from_seq(sy_half), n - 1, sz);
        let temp_int = Str2Int(temp_result@);
        let result_int = (temp_int * temp_int) % sz_int;
        return vec_from_seq(nat_to_bit_string(result_int, 1));
    } else {
        let sy_minus_one = sy_int - 1;
        let sy_new = nat_to_bit_string(sy_minus_one, n as usize);
        let temp_result = ModExpPow2(sx, &vec_from_seq(sy_new), n - 1, sz);
        let temp_int = Str2Int(temp_result@);
        let result_int = (sx_int * temp_int) % sz_int;
        return vec_from_seq(nat_to_bit_string(result_int, 1));
    }
}
// </vc-code>

fn main() {}
}


