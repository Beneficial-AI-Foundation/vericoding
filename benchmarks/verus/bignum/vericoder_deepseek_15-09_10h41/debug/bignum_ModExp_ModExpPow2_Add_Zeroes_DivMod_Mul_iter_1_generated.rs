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

proof fn lemma_pow_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_pow_rec(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

spec fn valid_bitstring_char(c: char) -> bool {
    c == '0' || c == '1'
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_cons(s: Seq<char>, c: char)
    requires ValidBitString(s.push(c)), s.len() == 0 || ValidBitString(s)
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 })
{
}

proof fn lemma_div_mod_same_base(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a + b) % m == (a % m + b % m) % m
{
}

proof fn lemma_mul_mod_base(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

proof fn lemma_modular_exponentiation_base(x: nat, y: nat, m: nat)
    requires m > 0
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
    decreases y
{
    if y > 0 {
        lemma_modular_exponentiation_base(x, (y - 1) as nat, m);
    }
}

proof fn lemma_exp_int_positive(x: nat, y: nat)
    ensures Exp_int(x, y) >= 1 || y == 0
{
}

proof fn lemma_str2int_nonnegative(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_exp_int_positive(Str2Int(sx@), Str2Int(sy@));
        lemma_str2int_nonnegative(sx@);
        lemma_str2int_nonnegative(sy@);
        lemma_str2int_nonnegative(sz@);
    }
    
    if sy.len() == 0 {
        proof { lemma_pow_zero(Str2Int(sx@)); }
        return vec!['1'];
    }
    
    let mut result: Vec<char> = Vec::new();
    let mut temp_x = Str2Int(sx@) % Str2Int(sz@);
    let mut temp_y = Str2Int(sy@);
    let m = Str2Int(sz@);
    
    proof {
        lemma_modular_exponentiation_base(Str2Int(sx@), temp_y, m);
    }
    
    while temp_y > 0
        invariant
            Exp_int(Str2Int(sx@), temp_y) % m == Exp_int(temp_x, temp_y) % m,
            temp_y <= Str2Int(sy@),
            m > 1
        decreases temp_y
    {
        if temp_y % 2 == 1 {
            proof {
                lemma_mul_mod_base(Exp_int(temp_x, temp_y - 1), temp_x, m);
            }
            result = vec!['1'];
        } else {
            result = vec!['0'];
        }
        temp_x = (temp_x * temp_x) % m;
        temp_y = temp_y / 2;
    }
    
    proof {
        lemma_pow_zero(temp_x);
    }
    
    result
}
// </vc-code>

fn main() {}
}
