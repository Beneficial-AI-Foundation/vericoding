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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>

proof fn lemma_str2int_nonnegative(s: Seq<char>) 
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        lemma_str2int_nonnegative(s_prefix);
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
    }
}

proof fn lemma_exp_int_nonnegative(x: nat, y: nat) 
    ensures Exp_int(x, y) >= 0
    decreases y
{
    if y == 0 {
        assert(Exp_int(x, y) == 1);
    } else {
        lemma_exp_int_nonnegative(x, (y - 1) as nat);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

proof fn lemma_mod_exp_property(x: nat, y: nat, z: nat) 
    requires z > 1
    ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z
    decreases y
{
    if y == 0 {
        assert(Exp_int(x, y) == 1);
        assert(Exp_int(x % z, y) == 1);
    } else {
        lemma_mod_exp_property(x, (y - 1) as nat, z);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x % z, y) == (x % z) * Exp_int(x % z, (y - 1) as nat));
        assert((x * Exp_int(x, (y - 1) as nat)) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z);
    }
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let mut base = Str2Int(sx@) % Str2Int(sz@);
    let mut exponent = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    let mut result = 1nat;
    
    while exponent > 0
        invariant
            result == Exp_int(base, exponent) % modulus,
            base < modulus,
            exponent >= 0,
        decreases exponent
    {
        if exponent % 2 == 1 {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
        exponent = exponent / 2;
    }
    
    proof {
        lemma_mod_exp_property(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        assert(result == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    let mut res_vec = Vec::new();
    let mut current = result;
    
    while current > 0
        invariant
            current >= 0,
        decreases current
    {
        if current % 2 == 0 {
            res_vec.push('0');
        } else {
            res_vec.push('1');
        }
        current = current / 2;
    }
    
    if res_vec.is_empty() {
        res_vec.push('0');
    }
    
    res_vec.reverse();
    res_vec
}
// </vc-code>

fn main() {}
}


