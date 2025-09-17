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
/* helper modified by LLM (iteration 4): fixed nat literal syntax and comparison operators */
exec fn char_to_nat(c: char) -> (result: nat)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
            (c == '0') ==> (result == 0),
            (c == '1') ==> (result == 1)
{
    if c == '1' { 1nat } else { 0nat }
}

exec fn nat_to_char(n: nat) -> (result: char)
    requires n == 0 || n == 1
    ensures result == '0' || result == '1',
            (n == 0) ==> (result == '0'),
            (n == 1) ==> (result == '1')
{
    if n == 1nat { '1' } else { '0' }
}

exec fn int_to_bitstring(mut n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@),
            result@.len() > 0
{
    let mut bits = Vec::new();
    if n == 0nat {
        bits.push('0');
        return bits;
    }
    while n > 0nat
        invariant ValidBitString(bits@)
        decreases n
    {
        if n % 2nat == 1nat {
            bits.push('1');
        } else {
            bits.push('0');
        }
        n = n / 2nat;
    }
    let mut result = Vec::new();
    let mut i = bits.len();
    while i > 0
        invariant ValidBitString(result@)
        decreases i
    {
        i = i - 1;
        result.push(bits[i]);
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed nat literal syntax and type conversions */
    if sy.len() == 0 {
        return Vec::new();
    }
    
    let mut result_val = 1nat;
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    let mut i = 0nat;
    while i < exp
        invariant result_val * Exp_int(base, exp - i) % modulus == Exp_int(Str2Int(sx@), Str2Int(sy@)) % modulus
        decreases exp - i
    {
        result_val = (result_val * base) % modulus;
        i = i + 1nat;
    }
    
    int_to_bitstring(result_val)
}
// </vc-code>

fn main() {}
}
