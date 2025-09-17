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

// <vc-helpers>
/* helper modified by LLM (iteration 4): converted to ghost functions for proper nat/int usage */
proof fn convert_str2int_to_int(s: Seq<char>) -> (val: int)
    requires ValidBitString(s)
    ensures val == Str2Int(s) as int
{
}

proof fn convert_len_to_int(s: Seq<char>) -> (len: int)
    ensures len == s.len() as int
{
}

proof fn lemma_mod_arithmetic(a: int, b: int, m: int)
    requires m > 1, a >= 0, b >= 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m,
            (a + b) % m == ((a % m) + (b % m)) % m
{
}

proof fn lemma_mod_exp(x: int, y: int, m: int)
    requires m > 1, x >= 0, y >= 0
    ensures Exp_int(x as nat, y as nat) as int % m == Exp_int(x as nat, y as nat) % m as nat
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed type conversion using ghost functions */
{
    proof {
        let m_int = convert_str2int_to_int(sz@);
        let x_val_int = convert_str2int_to_int(sx@) % m_int;
        let sy_len_int = convert_len_to_int(sy@);
    }
    
    let mut result = 1;
    let mut i = 0;
    
    while i < sy@.len()
        invariant
            i <= sy@.len(),
            result == (Exp_int(Str2Int(sx@), Str2Int(sy@.subrange(i as int, sy@.len() as int))) as int % convert_str2int_to_int(sz@),
            result >= 0
        decreases sy@.len() - i
    {
        let bit = sy@[i];
        result = if bit == '1' {
            (result * (convert_str2int_to_int(sx@) % convert_str2int_to_int(sz@))) % convert_str2int_to_int(sz@)
        } else {
            result
        };
        i += 1;
    }
    
    let mut res_vec = Vec::new();
    let mut temp = result;
    if temp == 0 {
        res_vec.push('0');
    } else {
        while temp > 0
            invariant temp >= 0
            decreases temp
        {
            if temp % 2 == 0 {
                res_vec.push('0');
            } else {
                res_vec.push('1');
            }
            temp = temp / 2;
        }
        res_vec.reverse();
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}
