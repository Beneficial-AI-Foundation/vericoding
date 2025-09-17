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
exec fn binary_str_to_u128(s: &[char]) -> (res: u128)
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

/* helper modified by LLM (iteration 2): fixed compilation error by replacing v.reverse() with manual reversal */
exec fn u128_to_binary_str(n: u128) -> (res: Vec<char>)
{
    if n == 0 {
        return vec!['0'];
    }
    let mut v = Vec::new();
    let mut num = n;
    while num > 0 {
        let bit = if num % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        num = num / 2;
    }
    let len = v.len();
    let mut result = Vec::with_capacity(len);
    for i in 0..len {
        result.push(v[len - 1 - i]);
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
{
    /* code modified by LLM (iteration 2): no changes */
    let x = binary_str_to_u128(sx);
    let m = binary_str_to_u128(sz);
    let base_reduced = x % m;
    let mut result: u128 = 1;
    for i in 0..sy.len() {
        result = (result * result) % m;
        if sy[i] == '1' {
            result = (result * base_reduced) % m;
        }
    }
    u128_to_binary_str(result)
}
// </vc-code>

fn main() {}
}
