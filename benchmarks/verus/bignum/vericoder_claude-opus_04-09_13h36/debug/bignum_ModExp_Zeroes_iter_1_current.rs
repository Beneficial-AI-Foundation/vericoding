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

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
    } else if n == 1 {
    } else {
        lemma_str2int_int2str(n / 2);
        let s = Int2Str(n / 2);
        assert(Int2Str(n) == s.push(if n % 2 == 0 { '0' } else { '1' }));
        assert(Str2Int(Int2Str(n)) == 2 * Str2Int(s) + (if n % 2 == 0 { 0 } else { 1 }));
        assert(Str2Int(s) == n / 2);
        assert(n == 2 * (n / 2) + n % 2);
    }
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n == 0 {
    } else if n == 1 {
    } else {
        lemma_int2str_valid(n / 2);
    }
}

exec fn int_to_str(n: usize) -> (res: Vec<char>)
    ensures res@ == Int2Str(n as nat)
    decreases n
{
    if n == 0 {
        vec!['0']
    } else if n == 1 {
        vec!['1']
    } else {
        let mut v = int_to_str(n / 2);
        if n % 2 == 0 {
            v.push('0');
        } else {
            v.push('1');
        }
        v
    }
}

exec fn str_to_int(s: &[char]) -> (res: usize)
    requires ValidBitString(s@)
    ensures res as nat == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        0
    } else {
        let n = s.len() - 1;
        let prefix = str_to_int(&s[..n]);
        let last = s[n];
        2 * prefix + (if last == '1' { 1 } else { 0 })
    }
}

proof fn lemma_exp_mod(x: nat, y: nat, z: nat)
    requires y > 0, z > 1
    ensures Exp_int(x, y) % z == ((x % z) * Exp_int(x, (y - 1) as nat)) % z
{
    assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
}

proof fn lemma_exp_even(x: nat, y: nat)
    requires y > 0, y % 2 == 0
    ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
    decreases y
{
    if y == 2 {
        assert(Exp_int(x, 2) == x * x * 1);
        assert(Exp_int(x * x, 1) == x * x);
    } else {
        assert(y >= 2);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, (y - 1) as nat) == x * Exp_int(x, (y - 2) as nat));
        assert(Exp_int(x, y) == x * x * Exp_int(x, (y - 2) as nat));
        lemma_exp_even(x, (y - 2) as nat);
        assert(Exp_int(x, (y - 2) as nat) == Exp_int(x * x, (y - 2) / 2));
        assert((y - 2) / 2 == y / 2 - 1);
    }
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
    let x = str_to_int(sx);
    let y = str_to_int(sy);
    let z = str_to_int(sz);
    
    proof {
        assert(x as nat == Str2Int(sx@));
        assert(y as nat == Str2Int(sy@));
        assert(z as nat == Str2Int(sz@));
    }
    
    if y == 0 {
        proof {
            assert(Exp_int(x as nat, 0) == 1);
            assert(1 % z as nat < z as nat);
            lemma_int2str_valid(1 % z as nat);
            lemma_str2int_int2str(1 % z as nat);
        }
        return int_to_str(1 % z);
    } else if y == 1 {
        proof {
            assert(Exp_int(x as nat, 1) == x as nat);
            assert(x as nat % z as nat < z as nat);
            lemma_int2str_valid(x as nat % z as nat);
            lemma_str2int_int2str(x as nat % z as nat);
        }
        return int_to_str(x % z);
    } else if y % 2 == 0 {
        let x_squared = (x * x) % z;
        let half_y_bits = int_to_str(y / 2);
        proof {
            lemma_int2str_valid(y / 2);
            assert(ValidBitString(half_y_bits@));
            lemma_str2int_int2str(y / 2);
            assert(Str2Int(half_y_bits@) == y / 2);
            assert(half_y_bits@.len() < sy@.len());
        }
        
        let x_squared_bits = int_to_str(x_squared);
        proof {
            lemma_int2str_valid(x_squared as nat);
            assert(ValidBitString(x_squared_bits@));
            lemma_str2int_int2str(x_squared as nat);
            assert(Str2Int(x_squared_bits@) == x_squared as nat);
        }
        
        let res = ModExp_Zeroes(&x_squared_bits, &half_y_bits, sz);
        proof {
            lemma_exp_even(x as nat, y as nat);
            assert(Exp_int(x as nat, y as nat) == Exp_int((x * x) as nat, y / 2));
            assert(Exp_int((x * x) as nat, y / 2) % z as nat == Exp_int(x_squared as nat, y / 2) % z as nat);
            assert(Str2Int(res@) == Exp_int(x_squared as nat, y / 2) % z as nat);
        }
        return res;
    } else {
        let y_minus_1 = y - 1;
        let y_minus_1_bits = int_to_str(y_minus_1);
        proof {
            lemma_int2str_valid(y_minus_1 as nat);
            assert(ValidBitString(y_minus_1_bits@));
            lemma_str2int_int2str(y_minus_1 as nat);
            assert(Str2Int(y_minus_1_bits@) == y_minus_1 as nat);
            assert(y_minus_1_bits@.len() < sy@.len());
        }
        
        let rec_res = ModExp_Zeroes(sx, &y_minus_1_bits, sz);
        let rec_val = str_to_int(&rec_res);
        let result = (x * rec_val) % z;
        
        proof {
            assert(Str2Int(rec_res@) == Exp_int(x as nat, (y - 1) as nat) % z as nat);
            assert(rec_val as nat == Str2Int(rec_res@));
            lemma_exp_mod(x as nat, y as nat, z as nat);
            assert(Exp_int(x as nat, y as nat) % z as nat == ((x as nat % z as nat) * Exp_int(x as nat, (y - 1) as nat)) % z as nat);
            assert(result as nat == (x as nat * rec_val as nat) % z as nat);
            lemma_int2str_valid(result as nat);
            lemma_str2int_int2str(result as nat);
        }
        
        return int_to_str(result);
    }
}
// </vc-code>

fn main() {}
}