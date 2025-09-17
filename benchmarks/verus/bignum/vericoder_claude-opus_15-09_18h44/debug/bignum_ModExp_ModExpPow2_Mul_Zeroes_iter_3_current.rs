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
/* helper modified by LLM (iteration 3): Fixed slice indexing to use usize */
proof fn exp_mod_properties()
    ensures
        forall |x: nat, n: nat| n > 0 ==> #[trigger] Exp_int(x, 0) % n == 1nat % n,
        forall |x: nat, y: nat, n: nat| n > 0 && y > 0 ==> Exp_int(x, y) % n == ((x % n) * (Exp_int(x, (y - 1) as nat) % n)) % n,
{ }

proof fn str2int_properties()
    ensures
        forall |s: Seq<char>| #[trigger] ValidBitString(s) && s.len() == 0 ==> Str2Int(s) == 0,
        forall |s: Seq<char>, c: char| ValidBitString(s) && (c == '0' || c == '1') ==> ValidBitString(s.push(c)),
{ }

exec fn compute_mod_exp(x_val: u64, y_val: u64, z_val: u64) -> (res: u64)
    requires
        z_val > 1,
    ensures
        res == Exp_int(x_val as nat, y_val as nat) % (z_val as nat),
    decreases y_val,
{
    if y_val == 0 {
        proof { exp_mod_properties(); }
        1 % z_val
    } else {
        proof { exp_mod_properties(); }
        let x_mod = x_val % z_val;
        let sub_res = compute_mod_exp(x_val, y_val - 1, z_val);
        (x_mod * sub_res) % z_val
    }
}

exec fn str_to_u64(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        Str2Int(s@) < u64::MAX,
    ensures
        res as nat == Str2Int(s@),
    decreases s@.len(),
{
    if s.len() == 0 {
        0
    } else {
        let last_idx = (s.len() - 1) as usize;
        let prefix = &s[..last_idx];
        let last = s[last_idx];
        let prefix_val = str_to_u64(prefix);
        2 * prefix_val + if last == '1' { 1 } else { 0 }
    }
}

exec fn u64_to_str(mut n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n as nat,
    decreases n,
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
    } else {
        while n > 0
            invariant
                ValidBitString(result@),
                n < u64::MAX,
            decreases n,
        {
            if n % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            n = n / 2;
        }
        result.reverse();
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Implementation of modular exponentiation */
    let x_val = str_to_u64(sx);
    let y_val = str_to_u64(sy);
    let z_val = str_to_u64(sz);
    
    let result_val = compute_mod_exp(x_val, y_val, z_val);
    
    let result = u64_to_str(result_val);
    
    proof {
        exp_mod_properties();
        str2int_properties();
    }
    
    result
}
// </vc-code>

fn main() {}
}
