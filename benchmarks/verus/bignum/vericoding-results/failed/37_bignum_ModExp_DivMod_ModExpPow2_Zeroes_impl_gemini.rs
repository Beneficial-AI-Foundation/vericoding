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
proof fn lemma_str2int_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 }),
        ValidBitString(s.push(c)),
{
}

exec fn str_to_int(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut i: usize = 0;
    let mut res: nat = 0;
    while i < s.len()
        invariant
            ValidBitString(s@),
            i <= s@.len(),
            res == Str2Int(s@.take(i as int)),
    {
        proof {
            lemma_str2int_push(s@.take(i as int), s@[i]);
        }
        res = res * 2;
        if s[i] == '1' {
            res = res + 1;
        }
        i = i + 1;
    }
    res
}

exec fn int_to_str(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n,
        n > 0 ==> res@.len() > 0 && res@[0] == '1',
        n == 0 ==> res@ == seq!['0'],
    decreases n
{
    if n == 0 {
        return vec!['0'];
    }
    if n < 2 { 
        return vec!['1'];
    }
    let prev_v = int_to_str(n / 2);
    let mut res = prev_v;
    let remainder = n % 2;
    if remainder == 1 {
        res.push('1');
    } else {
        res.push('0');
    }
    proof {
        vstd::arithmetic::internals::div_mod_proof(n, 2);
        let bit = if remainder == 1 { '1' } else { '0' };
        lemma_str2int_push(prev_v@, bit);
    }
    res
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
    let x = str_to_int(sx);
    let z = str_to_int(sz);

    if sy.len() == 1 {
        let res_val = if sy[0] == '1' { x % z } else { 1 };
        proof {
            let y_spec = Str2Int(sy@);
            assert(y_spec == if sy[0] == '1' { 1 } else { 0 });
            if y_spec == 1 {
                assert(Exp_int(x, y_spec) % z == x % z);
            } else {
                assert(Exp_int(x, y_spec) % z == 1 % z);
                assert(z > 1) by { }; 
                assert(1 % z == 1);
            }
        }
        return int_to_str(res_val);
    }

    let sy_prefix = &sy[..sy.len() - 1];
    let last_bit = sy[sy.len() - 1];

    let rec_res_v = ModExp_DivMod_ModExpPow2_Zeroes(sx, sy_prefix, sz);
    let rec_res = str_to_int(&rec_res_v);
    let sq = (rec_res * rec_res) % z;
    
    let final_res_val = if last_bit == '1' {
        (sq * x) % z
    } else {
        sq
    };

    proof {
        let y = Str2Int(sy@);
        let y_prefix = Str2Int(sy_prefix@);
        let last_bit_val = if last_bit == '1' { 1 } else { 0 };
        
        lemma_str2int_push(sy_prefix@, last_bit);
        assert(y == 2 * y_prefix + last_bit_val);

        let rec_res_spec = Exp_int(x, y_prefix) % z;
        assert(rec_res == rec_res_spec);

        vstd::arithmetic::power::lemma_exp_add(x, y_prefix, y_prefix);
        if last_bit == '1' {
            vstd::arithmetic::power::lemma_exp_add(x, 2 * y_prefix, 1);
        }
    }

    int_to_str(final_res_val)
}
// </vc-code>

fn main() {}
}
