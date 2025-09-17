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
/* helper modified by LLM (iteration 9): Corrected the base case handling for `nat_to_vchar_vector` for `n == 0` to ensure a consistent return type, and ensured `Seq` operations are correctly used for a `Seq<char>` return. */
spec fn nat_to_vchar_vector(n: nat) -> Seq<char>
decreases n
{
    if n == 0 { Seq::singleton('0') }
    else {
        let rem_val = n % 2;
        let div_val = n / 2;
        if div_val == 0 { Seq::singleton(if rem_val == 1 { '1' } else { '0' }) }
        else { nat_to_vchar_vector(div_val).push(if rem_val == 1 { '1' } else { '0' }) }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Removed `as nat` casts that were causing compilation errors on `nat` types. Converted `let y_minus_1: nat = (y - 1);` to `let y_minus_1: nat = (y - 1);` directly as `y` is already `nat`. */
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    
    if y == 0nat { 
        return Seq::singleton('1').to_vec();
    } else if y == 1nat { 
        let mut val: nat = x % z;
        let mut vec_result: Vec<char> = Vec::new();
        while val > 0nat
            invariant
                val >= 0nat,
                ValidBitString(vec_result@),
        {
            if val % 2nat == 1nat { 
                vec_result.insert(0, '1');
            } else {
                vec_result.insert(0, '0');
            }
            val = val / 2nat;
        }
        if vec_result.is_empty() { vec_result.insert(0, '0'); }
        return vec_result;
    } else {
        let y_minus_1: nat = (y - 1);
        let sy_prime_seq = nat_to_vchar_vector(y_minus_1);
        let sy_prime_vec = sy_prime_seq.to_vec();
        
        let res_pow_sub = ModExp_Add_ModExpPow2(sx, &sy_prime_vec.as_slice(), sz);
        
        let r = (x * Str2Int(res_pow_sub@)) % z;
        
        let mut val: nat = r;
        let mut vec_result: Vec<char> = Vec::new();
        while val > 0nat
            invariant
                val >= 0nat,
                ValidBitString(vec_result@),
        {
            if val % 2nat == 1nat { 
                vec_result.insert(0, '1');
            } else {
                vec_result.insert(0, '0');
            }
            val = val / 2nat;
        }
        if vec_result.is_empty() { vec_result.insert(0, '0'); }
        return vec_result;
    }
}
// </vc-code>

fn main() {}
}
