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
proof fn exp_mod_properties(x: nat, y: nat, z: nat)
    requires
        z > 1
    ensures
        y == 0 ==> Exp_int(x, y) % z == 1nat % z,
        y > 0 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
    decreases y
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert((x * Exp_int(x, (y - 1) as nat)) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z);
    }
}

fn str_to_int_exec(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        s@.len() <= 64
    ensures
        res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2 + if s[i] == '1' { 1 } else { 0 };
        i = i + 1;
    }
    
    result
}

fn int_to_str_exec(mut n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    
    if n == 0 {
        result.push('0');
        return result;
    }
    
    while n > 0
        invariant
            ValidBitString(result@)
    {
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    
    let mut i: usize = 0;
    let mut j: usize = result.len() - 1;
    
    while i < j
        invariant
            0 <= i <= j < result.len(),
            ValidBitString(result@)
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        if j > 0 { j = j - 1; }
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
    /* code modified by LLM (iteration 4): Fixed nat literal syntax errors */
    if sy@.len() == 0 || (sy@[0] == '0' && sy@.len() == 1) {
        let mut res = Vec::<char>::new();
        res.push('1');
        proof {
            assert(Str2Int(sy@) == 0);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            assert(1 % Str2Int(sz@) < Str2Int(sz@));
        }
        return int_to_str_exec((1 % str_to_int_exec(sz)) as u64);
    }
    
    let x_val = str_to_int_exec(sx);
    let y_val = str_to_int_exec(sy);
    let z_val = str_to_int_exec(sz);
    
    if y_val == 1 {
        proof {
            assert(Exp_int(x_val as nat, 1) == x_val as nat);
        }
        return int_to_str_exec((x_val % z_val) as u64);
    }
    
    let mut sy_minus_one = Vec::<char>::new();
    let y_minus_one = y_val - 1;
    sy_minus_one = int_to_str_exec(y_minus_one as u64);
    
    let recursive_result = ModExp_Add_DivMod_Zeroes(sx, &sy_minus_one, sz);
    let recursive_val = str_to_int_exec(&recursive_result);
    
    let x_mod = x_val % z_val;
    let result_val = ((x_mod * recursive_val) % z_val) as u64;
    
    proof {
        exp_mod_properties(x_val as nat, y_val as nat, z_val as nat);
        assert(Exp_int(x_val as nat, y_val as nat) % (z_val as nat) == ((x_val % z_val) as nat * (Exp_int(x_val as nat, (y_val - 1) as nat) % (z_val as nat))) % (z_val as nat));
        assert(recursive_val == Exp_int(x_val as nat, (y_val - 1) as nat) % (z_val as nat));
        assert(result_val == Exp_int(x_val as nat, y_val as nat) % (z_val as nat));
    }
    
    return int_to_str_exec(result_val);
}
// </vc-code>

fn main() {}
}
