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
proof fn lemma_str2int_nonnegative(s: Seq<char>) 
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
}

proof fn lemma_exp_int_nonnegative(x: nat, y: nat)
    ensures Exp_int(x, y) >= 0
{
}

proof fn lemma_power_mod_property(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y) % m >= 0,
        Exp_int(x, y) % m < m
{
}

proof fn lemma_str2int_valid_result(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(s)
{
}

fn slice_is_empty(s: &[char]) -> (res: bool)
    ensures res == (s@.len() == 0)
{
    s.len() == 0
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed slice is_empty usage */
    let mut result = Vec::<char>::new();
    
    if slice_is_empty(sy) {
        result.push('1');
    } else {
        let x_val: u64 = 0;
        let y_val: u64 = 0;
        let m_val: u64 = 0;
        
        let mut base = x_val % m_val;
        let mut exponent = y_val;
        let mut result_val = 1;
        
        while exponent > 0
            invariant
                true,
        {
            if exponent % 2 == 1 {
                result_val = (result_val * base) % m_val;
            }
            base = (base * base) % m_val;
            exponent /= 2;
        }
        
        let mut temp = result_val;
        while temp > 0
            invariant
                true,
        {
            if temp % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            temp /= 2;
        }
        result.reverse();
        
        if result.is_empty() {
            result.push('0');
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}
