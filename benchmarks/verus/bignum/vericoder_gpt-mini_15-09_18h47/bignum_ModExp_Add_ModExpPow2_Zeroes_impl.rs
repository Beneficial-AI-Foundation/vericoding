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
/* helper modified by LLM (iteration 3): convert slice of chars to nat */
fn slice_to_nat(a: &[char]) -> nat
    requires
        ValidBitString(a@),
    ensures
        result == Str2Int(a@),
{
    let mut r: nat = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            r == Str2Int(a@.subrange(0, i as int)),
        decreases a.len() - i
    {
        let bit = a[i];
        if bit == '1' {
            r = 2 * r + 1;
        } else {
            r = 2 * r;
        }
        i += 1;
    }
    r
}

/* helper modified by LLM (iteration 3): convert nat modulo base to bit vector */
fn nat_to_bitvec_mod(n: nat, base: nat) -> Vec<char>
    requires
        base > 1,
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n % base,
{
    let mut x: nat = n % base;
    let mut v_ls: Vec<char> = Vec::<char>::new();
    if x == 0 {
        v_ls.push('0');
    } else {
        while x > 0
            invariant
                0 <= x,
            decreases x
        {
            if x % 2 == 1 {
                v_ls.push('1');
            } else {
                v_ls.push('0');
            }
            x = x / 2;
        }
    }
    let mut v_ms: Vec<char> = Vec::<char>::new();
    let len: usize = v_ls.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i && i <= len,
        decreases len - i
    {
        v_ms.push(v_ls[len - 1 - i]);
        i += 1;
    }
    v_ms
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fast modular exponentiation using helpers */
    let x: nat = slice_to_nat(sx);
    let y: nat = slice_to_nat(sy);
    let m: nat = slice_to_nat(sz);

    let mut base: nat = x;
    let mut exp: nat = y;
    let mut acc: nat = 1;

    while exp > 0
        invariant
            0 <= exp,
            acc * Exp_int(base, exp) == Exp_int(x, y),
        decreases exp
    {
        let old_acc = acc;
        let old_base = base;
        let old_exp = exp;

        if old_exp % 2 == 1 {
            // consume one factor
            acc = old_acc * old_base;
            exp = old_exp - 1;
        }

        // halve the exponent and square the base
        exp = exp / 2;
        base = old_base * old_base;

        proof {
            if old_exp % 2 == 1 {
                // old_exp = 2*q + 1
                assert(old_exp >= 1);
                // Exp_int(old_base, old_exp) = old_base * Exp_int(old_base * old_base, old_exp / 2)
                assert(Exp_int(old_base, old_exp) == old_base * Exp_int(old_base * old_base, old_exp / 2));
                // acc * Exp_int(base, exp) == (old_acc * old_base) * Exp_int(old_base * old_base, old_exp / 2)
                assert(acc * Exp_int(base, exp) == (old_acc * old_base) * Exp_int(old_base * old_base, old_exp / 2));
                // which equals old_acc * Exp_int(old_base, old_exp)
                assert(acc * Exp_int(base, exp) == old_acc * Exp_int(old_base, old_exp));
            } else {
                // old_exp = 2*q
                assert(Exp_int(old_base, old_exp) == Exp_int(old_base * old_base, old_exp / 2));
                assert(acc * Exp_int(base, exp) == old_acc * Exp_int(old_base * old_base, old_exp / 2));
                assert(acc * Exp_int(base, exp) == old_acc * Exp_int(old_base, old_exp));
            }
        }
    }

    // when loop ends exp == 0, so acc == Exp_int(x,y)
    let res = nat_to_bitvec_mod(acc % m, m);
    res
}
// </vc-code>

fn main() {}
}
