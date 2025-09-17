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
/* helper modified by LLM (iteration 2): Fixed type usage for executable code */
proof fn lemma_exp_int_split(x: nat, y: nat)
    ensures
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
    if y > 0 {
        reveal(Exp_int);
    }
}

proof fn lemma_exp_int_mod(x: nat, y: nat, z: nat)
    requires
        z > 1,
        y > 0
    ensures
        Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
    lemma_exp_int_split(x, y);
    assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    assert(Exp_int(x, y) % z == (x * Exp_int(x, (y - 1) as nat)) % z);
    assert((x * Exp_int(x, (y - 1) as nat)) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z) by {
        let a = x;
        let b = Exp_int(x, (y - 1) as nat);
        assert((a * b) % z == ((a % z) * (b % z)) % z);
    }
}

exec fn int_to_bit_string(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n as nat
    decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let mut res = int_to_bit_string(n / 2);
        if n % 2 == 1 {
            res.push('1');
        } else {
            res.push('0');
        }
        res
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type usage for executable code */
    let ghost x = Str2Int(sx@);
    let ghost y = Str2Int(sy@);
    let ghost z = Str2Int(sz@);
    
    if sy.len() == 0 {
        assert(y == 0);
        assert(Exp_int(x, y) == 1) by { reveal(Exp_int); }
        let result = int_to_bit_string(1u64);
        assert(1u64 as nat % z == (1 % z) as nat);
        assert(Str2Int(result@) == 1);
        assert(1 % z == Exp_int(x, y) % z);
        return result;
    } else if sy[sy.len() - 1] == '0' {
        let sy_half = &sy[0..sy.len() - 1];
        assert(ValidBitString(sy_half@));
        assert(Str2Int(sy@) == 2 * Str2Int(sy_half@)) by {
            reveal(Str2Int);
        }
        
        let temp = ModExp_DivMod_ModExpPow2_Zeroes(sx, sy_half, sz);
        assert(Str2Int(temp@) == Exp_int(x, Str2Int(sy_half@)) % z);
        
        let ghost temp_val = Str2Int(temp@);
        let exec_temp_val = temp_to_u64(&temp);
        let exec_res_val = (exec_temp_val * exec_temp_val) % sz_to_u64(sz);
        
        proof {
            assert(y == 2 * Str2Int(sy_half@));
            assert(Exp_int(x, y) == Exp_int(Exp_int(x, Str2Int(sy_half@)), 2)) by {
                reveal(Exp_int);
                assert(Exp_int(x, y) == Exp_int(x, 2 * Str2Int(sy_half@)));
            }
            assert(Exp_int(Exp_int(x, Str2Int(sy_half@)), 2) == Exp_int(x, Str2Int(sy_half@)) * Exp_int(x, Str2Int(sy_half@))) by {
                reveal(Exp_int);
            }
            assert(Exp_int(x, y) % z == ((Exp_int(x, Str2Int(sy_half@)) % z) * (Exp_int(x, Str2Int(sy_half@)) % z)) % z);
            assert(exec_res_val as nat == ((temp_val * temp_val) % z));
        }
        
        return int_to_bit_string(exec_res_val);
    } else {
        assert(sy[sy.len() - 1] == '1');
        let sy_minus_one = if sy.len() == 1 {
            Vec::<char>::new()
        } else {
            let mut v = Vec::<char>::new();
            for i in 0..(sy.len() - 1) {
                v.push(sy[i]);
            }
            v[v.len() - 1] = '0';
            v
        };
        
        assert(ValidBitString(sy_minus_one@));
        assert(Str2Int(sy@) == Str2Int(sy_minus_one@) + 1) by {
            reveal(Str2Int);
        }
        
        let temp = ModExp_DivMod_ModExpPow2_Zeroes(sx, &sy_minus_one, sz);
        let exec_x_mod = sx_to_u64(sx) % sz_to_u64(sz);
        let exec_temp_val = temp_to_u64(&temp);
        let exec_res_val = (exec_x_mod * exec_temp_val) % sz_to_u64(sz);
        
        proof {
            lemma_exp_int_mod(x, y, z);
            assert(exec_res_val as nat == ((x % z) * Str2Int(temp@)) % z);
        }
        
        return int_to_bit_string(exec_res_val);
    }
}

exec fn temp_to_u64(v: &Vec<char>) -> (res: u64)
    requires ValidBitString(v@)
    ensures res as nat == Str2Int(v@)
{
    let mut result = 0u64;
    for i in 0..v.len() {
        result = result * 2;
        if v[i] == '1' {
            result = result + 1;
        }
    }
    result
}

exec fn sx_to_u64(sx: &[char]) -> (res: u64)
    requires ValidBitString(sx@)
    ensures res as nat == Str2Int(sx@)
{
    let mut result = 0u64;
    for i in 0..sx.len() {
        result = result * 2;
        if sx[i] == '1' {
            result = result + 1;
        }
    }
    result
}

exec fn sz_to_u64(sz: &[char]) -> (res: u64)
    requires ValidBitString(sz@), Str2Int(sz@) > 1
    ensures res as nat == Str2Int(sz@)
{
    let mut result = 0u64;
    for i in 0..sz.len() {
        result = result * 2;
        if sz[i] == '1' {
            result = result + 1;
        }
    }
    result
}
// </vc-code>

fn main() {}
}
