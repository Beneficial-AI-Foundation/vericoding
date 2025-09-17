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
proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_one(x: nat)
    ensures Exp_int(x, 1) == x
{
}

proof fn lemma_exp_mod(x: nat, y: nat, z: nat)
    requires z > 0
    ensures Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
    decreases y
{
    if y == 0 {
    } else {
        lemma_exp_mod(x, (y - 1) as nat, z);
    }
}

proof fn lemma_str2int_zero(s: Seq<char>)
    requires s.len() == 1,
        s[0] == '0'
    ensures Str2Int(s) == 0
{
}

proof fn lemma_str2int_pow2(n: nat) -> (s: Seq<char>)
    ensures ValidBitString(s),
        s.len() == n + 1,
        Str2Int(s) == Exp_int(2, n)
    decreases n
{
    if n == 0 {
        s = seq!['1'];
    } else {
        let prev = lemma_str2int_pow2((n - 1) as nat);
        s = prev.push('0');
    }
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
    if sy.len() == 1 && sy[0] == '0' {
        proof {
            lemma_str2int_zero(sy@);
            lemma_exp_zero(Str2Int(sx@));
        }
        return vec!['1'];
    }
    
    if n == 0 {
        proof {
            lemma_exp_one(Str2Int(sx@));
        }
        let mut result = Vec::<char>::new();
        let x_val = Str2Int(sx@);
        let z_val = Str2Int(sz@);
        let mod_val = (x_val % z_val) as u64;
        let mut temp = mod_val;
        if temp == 0 {
            result.push('0');
        } else {
            let mut digits = Vec::<char>::new();
            while temp > 0 {
                if temp % 2 == 1 {
                    digits.push('1');
                } else {
                    digits.push('0');
                }
                temp = temp / 2;
            }
            let mut i = digits.len() as i64 - 1;
            while i >= 0 {
                result.push(digits[i as usize]);
                i = i - 1;
            }
        }
        return result;
    }
    
    let mut half_y = Vec::<char>::new();
    for i in 0..sy.len() - 1 {
        half_y.push(sy[i]);
    }
    
    let half_result = ModExpPow2(sx, &half_y, n - 1, sz);
    let squared = ModExpPow2(&half_result, &vec!['1', '0'], 1, sz);
    
    proof {
        lemma_exp_mod(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
    }
    
    return squared;
}
// </vc-code>

fn main() {}
}


