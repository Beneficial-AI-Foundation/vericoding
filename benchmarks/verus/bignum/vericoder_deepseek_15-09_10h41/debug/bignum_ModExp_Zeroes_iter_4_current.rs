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
/* helper modified by LLM (iteration 4): fixed helper function signature and ensures clause to use proper nat types */
fn to_u64(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() <= 64
    ensures res as nat == Str2Int(s@)
{
    let mut val: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i && i <= s@.len(),
            val as nat == Str2Int(s@.subrange(0, i as int)),
    {
        val = val * 2 + (if s[i] == '1' { 1 } else { 0 });
        i += 1;
    }
    val
}

/* helper modified by LLM (iteration 4): fixed helper function with proper ensures clause */
fn from_u64(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n as nat
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
    } else {
        while n > 0
            invariant
                n as nat >= 0,
                ValidBitString(result@),
                Str2Int(result@) == (n as nat) * Exp_int(2, result@.len() as nat),
        {
            if n % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            n /= 2;
        }
        result.reverse();
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed type conversion from int to nat in loop invariant */
{
    let x_val = to_u64(sx);
    let y_val = to_u64(sy);
    let m_val = to_u64(sz);
    
    let mut base = x_val % m_val;
    let mut exponent = y_val;
    let mut result_val = 1;
    
    while exponent > 0
        invariant
            result_val as nat == Exp_int((x_val as nat) % (m_val as nat), (y_val as nat - exponent as nat)) % (m_val as nat),
            exponent >= 0,
    {
        if exponent % 2 == 1 {
            result_val = (result_val * base) % m_val;
        }
        base = (base * base) % m_val;
        exponent /= 2;
    }
    
    let result = from_u64(result_val);
    result
}
// </vc-code>

fn main() {}
}
