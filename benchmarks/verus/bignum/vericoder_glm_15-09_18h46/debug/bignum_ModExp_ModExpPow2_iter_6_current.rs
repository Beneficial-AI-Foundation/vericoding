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
/* helper modified by LLM (iteration 5): fixed requires clause syntax */
exec fn binary_str_to_u128(s: &[char]) -> (res: u128)
    requires
        ValidBitString(s@),
        s.len() <= 128,
    ensures res == Str2Int(s@)
{
    let mut res = 0u128;
    for i in 0..s.len() {
        res = res * 2;
        if s[i] == '1' {
            res = res + 1;
        }
    }
    res
}

/* helper modified by LLM (iteration 6): fixed ensures clause syntax */
exec fn u128_to_binary_str(n: u128) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n,
{
    if n == 0 {
        return vec!['0'];
    }
    let mut v = Vec::new();
    let mut num = n;
    while num > 0
        decreases num
    {
        let bit = if num % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        num = num / 2;
    }
    let len = v.len();
    let mut result = Vec::with_capacity(len);
    let mut i = len;
    while i > 0
        invariant
            result.len() == len - i,
            i <= len,
            i >= 0,
    {
        i = i - 1;
        result.push(v[i]);
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed helper function syntax */
{
    let x_val = binary_str_to_u128(sx);
    let m_val = binary_str_to_u128(sz);
    let mask = m_val - 1;
    let base_reduced = x_val % m_val;
    let mut result: u128 = 1;
    for i in 0..sy.len() {
        result = (result * result) & mask;
        if sy[i] == '1' {
            result = (result * base_reduced) & mask;
        }
    }
    u128_to_binary_str(result)
}
// </vc-code>

fn main() {}
}
