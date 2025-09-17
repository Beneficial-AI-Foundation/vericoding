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
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* helper modified by LLM (iteration 4): Fixed Int2Vec signature and implementation */
fn Int2Vec(n: nat) -> Vec<char>
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut v = Int2Vec(n / 2);
        v.push(if n % 2 == 1 { '1' } else { '0' });
        v
    }
}

proof fn lemma_exp_mod_pow2_property()
    ensures true
{
}
// </vc-code>

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
/* code modified by LLM (iteration 4): Fixed function parameters and logic */
{
    if Str2Int(sy@) == 0 {
        return Int2Vec(1 % Str2Int(sz@));
    }
    let mut result = Int2Vec(Str2Int(sx@) % Str2Int(sz@));
    let base = result.clone();
    
    for i in 1..=n as usize {
        result = {
            let mut q = Vec::new();
            let mut r = Vec::new();
            let mut current = Vec::new();
            let divisor_val = Str2Int(sz@);
            
            for i in 0..result.len() {
                current.push(result[i]);
                let current_val = Str2Int(current@);
                
                if current_val >= divisor_val {
                    q.push('1');
                    let remainder_val = current_val % divisor_val;
                    current = Int2Vec(remainder_val);
                } else {
                    q.push('0');
                }
            }
            
            q
        };
        result = {
            let mut q = Vec::new();
            let mut r = Vec::new();
            let mut current = Vec::new();
            let divisor_val = Str2Int(sz@);
            
            for i in 0..result.len() {
                current.push(result[i]);
                let current_val = Str2Int(current@);
                
                if current_val >= divisor_val {
                    q.push('1');
                    let remainder_val = current_val % divisor_val;
                    current = Int2Vec(remainder_val);
                } else {
                    q.push('0');
                }
            }
            
            current
        };
    }
    
    result
}
// </vc-code>

fn main() {}
}


