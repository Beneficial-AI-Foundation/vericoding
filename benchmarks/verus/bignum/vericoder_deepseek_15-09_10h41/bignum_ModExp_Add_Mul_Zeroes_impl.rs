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
/* helper modified by LLM (iteration 5): Fixed type annotations and nat/int conversions */
proof fn lemma_pow_mod_property(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
{
    if y == 0 {
        assert(Exp_int(x, 0) % m == 1 % m);
        assert(1nat % m == 1nat);
        assert(Exp_int(x % m, 0) % m == 1 % m);
    } else {
        lemma_pow_mod_property(x, (y - 1) as nat, m);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x % m, y) == (x % m) * Exp_int(x % m, (y - 1) as nat));
    }
}

proof fn lemma_str2int_mod_property(s: Seq<char>, m: nat)
    requires ValidBitString(s), m > 1
    ensures Str2Int(s) % m == (2 * Str2Int(s.subrange(0, s.len() as int - 1)) % m + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })) % m
{
    if s.len() == 0 {
        assert(Str2Int(s) % m == 0nat % m);
    } else {
        lemma_str2int_mod_property(s.subrange(0, s.len() as int - 1), m);
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
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
/* code modified by LLM (iteration 5): Fixed nat/int conversions and while loop with proper nat handling */
{
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
    let partial_val = Str2Int(partial@);
    
    if y_head == '1' {
        let mut result = Vec::new();
        let x_mod = Str2Int(sx@) % Str2Int(sz@);
        let temp = (x_mod * partial_val) % Str2Int(sz@);
        
        let mut temp_vec = Vec::new();
        let mut n: nat = temp;
        while n > 0nat {
            if n % 2nat == 1nat {
                temp_vec.push('1');
            } else {
                temp_vec.push('0');
            }
            n = n / 2nat;
        }
        temp_vec.reverse();
        if temp_vec.is_empty() {
            temp_vec.push('0');
        }
        result.extend(temp_vec);
        return result;
    } else {
        return partial;
    }
}
// </vc-code>

fn main() {}
}
