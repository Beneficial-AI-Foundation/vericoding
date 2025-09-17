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
        Exp_int(x, 0) % z == 1 % z,
        y > 0 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
    if y > 0 {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        Int2Str(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
    }
}

proof fn int2str_valid(n: nat)
    ensures
        ValidBitString(Int2Str(n))
    decreases n
{
    if n > 1 {
        int2str_valid(n / 2);
    }
}

proof fn int2str_correct(n: nat)
    ensures
        ValidBitString(Int2Str(n)),
        Str2Int(Int2Str(n)) == n
    decreases n
{
    int2str_valid(n);
    if n == 0 {
        assert(Int2Str(0) == seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
    } else if n == 1 {
        assert(Int2Str(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else {
        int2str_correct(n / 2);
        let s = Int2Str(n / 2);
        let c = if n % 2 == 0 { '0' } else { '1' };
        assert(Int2Str(n) == s.push(c));
        assert(Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0}));
        assert(n == 2 * (n / 2) + n % 2);
    }
}

exec fn str_to_int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        s@.len() <= 64
    ensures
        res as nat == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result as nat == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2 + if s[i] == '1' { 1 } else { 0 };
        i = i + 1;
    }
    assert(s@.subrange(0, s@.len() as int) == s@);
    result
}

exec fn int_to_str(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n as nat
{
    proof {
        int2str_correct(n as nat);
    }
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
    } else {
        let mut temp = n;
        let mut digits = Vec::<char>::new();
        while temp > 0
            invariant
                ValidBitString(digits@)
        {
            digits.push(if temp % 2 == 0 { '0' } else { '1' });
            temp = temp / 2;
        }
        let mut i = digits.len();
        while i > 0
            invariant
                0 <= i <= digits.len(),
                ValidBitString(result@)
        {
            i = i - 1;
            result.push(digits[i]);
        }
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
{
    if sy@.len() == 1 && sy@[0] == '0' {
        proof {
            exp_mod_properties(Str2Int(sx@), 0, Str2Int(sz@));
        }
        let res_val = 1 % str_to_int(sz);
        return int_to_str(res_val);
    }
    
    let y_val = str_to_int(sy);
    if y_val == 1 {
        let x_val = str_to_int(sx);
        let z_val = str_to_int(sz);
        let res_val = x_val % z_val;
        return int_to_str(res_val);
    }
    
    let mut sy_minus_one = Vec::<char>::new();
    let mut carry = true;
    let mut i = sy.len();
    while i > 0
        invariant
            0 <= i <= sy.len(),
            ValidBitString(sy_minus_one@)
    {
        i = i - 1;
        if carry {
            if sy[i] == '1' {
                sy_minus_one.push('0');
                carry = false;
            } else {
                sy_minus_one.push('1');
            }
        } else {
            sy_minus_one.push(sy[i]);
        }
    }
    
    let mut sy_minus_one_rev = Vec::<char>::new();
    let mut j = sy_minus_one.len();
    while j > 0
        invariant
            0 <= j <= sy_minus_one.len(),
            ValidBitString(sy_minus_one_rev@)
    {
        j = j - 1;
        sy_minus_one_rev.push(sy_minus_one[j]);
    }
    
    let rec_result = ModExp_Zeroes(&sx, &sy_minus_one_rev, &sz);
    let x_val = str_to_int(sx);
    let z_val = str_to_int(sz);
    let rec_val = str_to_int(&rec_result);
    let res_val = ((x_val % z_val) * rec_val) % z_val;
    
    proof {
        exp_mod_properties(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
    }
    
    return int_to_str(res_val);
}
// </vc-code>

fn main() {}
}
