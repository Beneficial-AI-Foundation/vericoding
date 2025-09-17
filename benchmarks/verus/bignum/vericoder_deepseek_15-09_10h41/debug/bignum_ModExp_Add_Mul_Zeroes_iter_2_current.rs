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
proof fn lemma_pow_mod_property(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
{
    if y == 0 {
        assert(Exp_int(x, 0) % m == 1 % m);
        assert(1 % m == 1);
        assert(Exp_int(x % m, 0) % m == 1 % m);
    } else {
        lemma_pow_mod_property(x, y - 1, m);
        assert(Exp_int(x, y) == x * Exp_int(x, y - 1));
        assert(Exp_int(x % m, y) == (x % m) * Exp_int(x % m, y - 1));
    }
}

proof fn lemma_str2int_mod_property(s: Seq<char>, m: nat)
    requires ValidBitString(s), m > 1
    ensures Str2Int(s) % m == (2 * Str2Int(s.subrange(0, s.len() as int - 1)) % m + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 })) % m
{
    if s.len() == 0 {
        assert(Str2Int(s) % m == 0 % m);
    } else {
        lemma_str2int_mod_property(s.subrange(0, s.len() as int - 1), m);
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 }));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed compilation error and improved logic */
    if sy.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        proof {
            lemma_pow_mod_property(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        }
        return result;
    }
    
    let y_tail = &sy[1..];
    let y_head = sy[0];
    
    let partial = ModExp_Add_Mul_Zeroes(sx, y_tail, sz);
    
    let mut temp = Vec::new();
    if y_head == '1' {
        temp = ModExp_Add_Mul_Zeroes(sx, y_tail, sz);
        let mut result = Vec::new();
        for _ in 0..2 {
            result.extend(temp.iter().copied());
        }
        proof {
            lemma_str2int_mod_property(result@, Str2Int(sz@));
        }
        return result;
    } else {
        return partial;
    }
}
// </vc-code>

fn main() {}
}
