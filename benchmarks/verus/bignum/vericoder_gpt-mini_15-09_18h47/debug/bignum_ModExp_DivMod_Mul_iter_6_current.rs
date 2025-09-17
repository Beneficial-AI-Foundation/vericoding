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
/* helper modified by LLM (iteration 6): fix nat/int literals in exp_two_times */
proof fn exp_two_times(k: nat)
    ensures Exp_int(2nat, k + 1nat) == 2nat * Exp_int(2nat, k)
    decreases k
{
    if k == 0nat {
        proof {
            assert(Exp_int(2nat, 1nat) == 2nat * Exp_int(2nat, 0nat));
        }
    } else {
        exp_two_times(k - 1nat);
        proof {
            assert(Exp_int(2nat, k + 1nat) == 2nat * Exp_int(2nat, k));
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): implement modular exponentiation and binary conversion with nat literals */
    let base0: nat = Str2Int(sx@);
    let exp0: nat = Str2Int(sy@);
    let modn: nat = Str2Int(sz@);

    let mut pow_val: nat = 1nat;
    let mut e: nat = exp0;
    while e > 0nat
        invariant
            pow_val * Exp_int(base0, e) == Exp_int(base0, exp0),
        decreases e
    {
        pow_val = pow_val * base0;
        e = e - 1nat;
    }

    let r: nat = pow_val % modn;

    if r == 0nat {
        return Vec::<char>::new();
    }

    let mut pow2: nat = 1nat;
    let mut len: nat = 0nat;
    while pow2 <= r
        invariant
            pow2 == Exp_int(2nat, len),
        decreases r + 1nat - pow2
    {
        pow2 = pow2 * 2nat;
        len = len + 1nat;
    }

    let orig_r: nat = r;
    let mut i: nat = len;
    let mut rem: nat = r;
    let mut resv: Vec<char> = Vec::new();

    while i > 0nat
        invariant
            pow2 == Exp_int(2nat, i),
            rem + Str2Int(resv@) * Exp_int(2nat, i) == orig_r,
            rem < pow2,
        decreases i
    {
        i = i - 1nat;
        pow2 = pow2 / 2nat;
        let p: nat = pow2;
        if rem >= p {
            resv.push('1');
            rem = rem - p;
        } else {
            resv.push('0');
        }
    }

    resv
}
// </vc-code>

fn main() {}
}
