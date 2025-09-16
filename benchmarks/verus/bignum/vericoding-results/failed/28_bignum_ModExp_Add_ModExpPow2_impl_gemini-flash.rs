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
/* helper modified by LLM (iteration 10): Fixed `Seq::singleton` to `Seq::new` when creating a single character sequence and added `Seq::empty()` for the base case. */
spec fn nat_to_vchar_vector(n: nat) -> Seq<char>
decreases n
{
    if n == 0 { Seq::empty().push('0') }
    else {
        let rem_val = n % 2;
        let div_val = n / 2;
        if div_val == 0 { Seq::empty().push(if rem_val == 1 { '1' } else { '0' }) }
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
/* code modified by LLM (iteration 10): Removed `nat` suffix from number literals and replaced `to_vec()` with `into_vec()` on `Seq<char>` to `Vec<char>`. Handled `y-1` as `y.sub(1)` or `y - 1` with a `proof { y >= 1 }` assertion as required. */
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    
    if y == 0 {
        return Seq::empty().push('1').into_vec();
    } else if y == 1 {
        let mut val: nat = x % z;
        let mut vec_result: Vec<char> = Vec::new();
        while val > 0
            invariant
                val >= 0,
                ValidBitString(vec_result@),
        {
            if val % 2 == 1 {
                vec_result.insert(0, '1');
            } else {
                vec_result.insert(0, '0');
            }
            val = val / 2;
        }
        if vec_result.is_empty() { vec_result.insert(0, '0'); }
        return vec_result;
    } else {
        let y_minus_1: nat;
        proof {
            assert(y >= 1);
        }
        y_minus_1 = y - 1;
        let sy_prime_seq = nat_to_vchar_vector(y_minus_1 as nat);
        let sy_prime_vec = sy_prime_seq.into_vec();
        
        let res_pow_sub = ModExp_Add_ModExpPow2(sx, &sy_prime_vec.as_slice(), sz);
        
        let r = (x * Str2Int(res_pow_sub@)) % z;
        
        let mut val: nat = r;
        let mut vec_result: Vec<char> = Vec::new();
        while val > 0
            invariant
                val >= 0,
                ValidBitString(vec_result@),
        {
            if val % 2 == 1 {
                vec_result.insert(0, '1');
            } else {
                vec_result.insert(0, '0');
            }
            val = val / 2;
        }
        if vec_result.is_empty() { vec_result.insert(0, '0'); }
        return vec_result;
    }
}
// </vc-code>

fn main() {}
}
