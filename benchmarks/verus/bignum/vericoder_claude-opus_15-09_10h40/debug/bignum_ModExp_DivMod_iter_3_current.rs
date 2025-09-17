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
/* helper modified by LLM (iteration 3): Fixed type signatures to use u64 instead of nat for exec context */
proof fn lemma_exp_properties(x: u64, y: u64, z: u64)
    requires z > 1
    ensures
        Exp_int(x as nat, 0) == 1,
        y > 0 ==> Exp_int(x as nat, y as nat) == (x as nat) * Exp_int(x as nat, (y - 1) as nat),
        Exp_int((x % z) as nat, y as nat) % (z as nat) == Exp_int(x as nat, y as nat) % (z as nat)
{
}

proof fn lemma_mod_mul(a: u64, b: u64, m: u64)
    requires m > 0
    ensures ((a as nat) * (b as nat)) % (m as nat) == (((a % m) as nat) * ((b % m) as nat)) % (m as nat)
{
}

exec fn int_to_binary(mut n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    while n > 0
        invariant
            ValidBitString(result@),
            n < u64::MAX
        decreases n
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    result
}

exec fn binary_to_int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        Str2Int(s@) < u64::MAX
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result < u64::MAX
        decreases s.len() - i
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let x_val = binary_to_int(sx);
    let y_val = binary_to_int(sy);
    let z_val = binary_to_int(sz);
    
    let mut base = x_val % z_val;
    let mut exp = y_val;
    let mut result: u64 = 1;
    
    while exp > 0
        invariant
            z_val > 1,
            result < z_val,
            base < z_val
        decreases exp
    {
        if exp % 2 == 1 {
            proof {
                lemma_mod_mul(result, base, z_val);
            }
            result = (result * base) % z_val;
        }
        proof {
            lemma_mod_mul(base, base, z_val);
        }
        base = (base * base) % z_val;
        exp = exp / 2;
    }
    
    proof {
        lemma_exp_properties(x_val, y_val, z_val);
    }
    
    int_to_binary(result)
}
// </vc-code>

fn main() {}
}
