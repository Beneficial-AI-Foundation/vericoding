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
/* helper modified by LLM (iteration 5): fix nat literal type errors and ensure proper conversions */
proof fn lemma_exp_int_monotonic(x: nat, y1: nat, y2: nat)
    requires x > 0, y1 >= y2
    ensures Exp_int(x, y1) >= Exp_int(x, y2)
    decreases y1
{
    if y2 == 0 {
        assert(Exp_int(x, y2) == 1);
        assert(Exp_int(x, y1) >= 1);
    } else if y1 > y2 {
        lemma_exp_int_monotonic(x, (y1 - 1) as nat, (y2 - 1) as nat);
        assert(Exp_int(x, y1) == x * Exp_int(x, (y1 - 1) as nat));
        assert(Exp_int(x, y1) >= x * Exp_int(x, (y2 - 1) as nat));
        assert(Exp_int(x, y1) >= Exp_int(x, y2));
    }
}

proof fn lemma_str2int_nonnegative(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
    decreases s.len()
{
    if s.len() > 0 {
        lemma_str2int_nonnegative(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_mod_exp_property_base(a: nat, e: nat, m: nat)
    requires m > 1, a < m
    ensures Exp_int(a, e) % m == Exp_int(a, e)
    decreases e
{
    if e > 0 {
        lemma_mod_exp_property_base(a, (e - 1) as nat, m);
        assert(Exp_int(a, e) == a * Exp_int(a, (e - 1) as nat));
        assert(Exp_int(a, e) < m * Exp_int(a, (e - 1) as nat));
    }
}

proof fn lemma_mod_exp_property_step(a: nat, e: nat, m: nat)
    requires m > 1
    ensures Exp_int(a, e) % m == Exp_int(a % m, e) % m
    decreases e
{
    if e == 0 {
        assert(Exp_int(a, 0) == 1);
        assert(Exp_int(a % m, 0) == 1);
        assert(Exp_int(a, 0) % m == 1 % m);
        assert(Exp_int(a % m, 0) % m == 1 % m);
    } else {
        lemma_mod_exp_property_step(a, (e - 1) as nat, m);
        assert(Exp_int(a, e) == a * Exp_int(a, (e - 1) as nat));
        assert(Exp_int(a, e) % m == (a * Exp_int(a, (e - 1) as nat)) % m);
        assert(Exp_int(a, e) % m == ((a % m) * (Exp_int(a, (e - 1) as nat) % m)) % m);
        assert(Exp_int(a, e) % m == ((a % m) * (Exp_int(a % m, (e - 1) as nat) % m)) % m);
        assert(Exp_int(a, e) % m == Exp_int(a % m, e) % m);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix nat conversion by using integer operations with proper type annotations */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    proof {
        lemma_str2int_nonnegative(sx@);
        lemma_str2int_nonnegative(sy@);
        lemma_str2int_nonnegative(sz@);
        lemma_mod_exp_property_step(x_val, y_val, z_val);
    }
    
    let result_val = Exp_int(x_val % z_val, y_val) % z_val;
    
    let mut result_vec = Vec::<char>::new();
    if result_val == 0 {
        result_vec.push('0');
    } else {
        let mut n: int = result_val as int;
        while n > 0
            invariant
                n >= 0,
                ValidBitString(result_vec@),
                result_val == (n as nat) * Exp_int(2, result_vec@.len() as nat) + Str2Int(result_vec@)
            decreases n
        {
            if n % 2 == 1 {
                result_vec.push('1');
            } else {
                result_vec.push('0');
            }
            n = n / 2;
        }
        result_vec.reverse();
    }

    result_vec
}
// </vc-code>

fn main() {}
}
