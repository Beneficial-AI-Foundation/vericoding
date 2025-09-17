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
exec fn vec_to_nat(s: &[char]) -> nat
  ensures result == Str2Int(s@)
{
    let mut i: int = 0;
    let mut acc: nat = 0;
    while i < s.len() as int
        invariant 0 <= i && i <= s.len() as int;
        invariant acc == Str2Int(s@.subrange(0, i));
        decreases s.len() as int - i;
    {
        let ch = s[i as usize];
        // update acc = 2 * acc + bit
        acc = acc * 2 + (if ch == '1' { 1 } else { 0 });
        // prove the invariant for i+1
        {
            // By definition of Str2Int:
            // Str2Int(s@.subrange(0, i+1)) == 2 * Str2Int(s@.subrange(0, i)) + (if s@.index(i) == '1' {1} else {0})
            // s@.index(i) corresponds to s[i as usize] which is ch
            assert(acc == Str2Int(s@.subrange(0, i + 1)));
        }
        i += 1;
    }
    acc
}

exec fn pow_naive(a: nat, e: nat) -> nat
  ensures result == Exp_int(a, e)
{
    let mut e0: nat = e;
    let mut res: nat = 1;
    // invariant: res * Exp_int(a, e) == Exp_int(a, e0)
    while e > 0
        invariant res * Exp_int(a, e) == Exp_int(a, e0);
        invariant e <= e0;
        decreases e;
    {
        // Before update: res * Exp_int(a, e) == Exp_int(a, e0)
        // We will set res := res * a; e := e - 1;
        res = res * a;
        // use proof about Exp_int to update invariant
        {
            // Let old_e be e + 0 before decrement; after decrement new e is old_e - 1
            // We need to show: (res * a) * Exp_int(a, e - 1) == Exp_int(a, e0)
            // Rearranged: res * (a * Exp_int(a, e - 1)) == Exp_int(a, e0)
            // But a * Exp_int(a, e - 1) == Exp_int(a, e) when e > 0
            assert(a * Exp_int(a, e - 1) == Exp_int(a, e));
            // Now previous invariant gives res_old * Exp_int(a, e) == Exp_int(a, e0)
            // which implies new res * Exp_int(a, e - 1) == Exp_int(a, e0)
        }
        e = e - 1;
    }
    // When e == 0, invariant gives res * Exp_int(a, 0) == Exp_int(a, e0)
    // Exp_int(a,0) == 1, so res == Exp_int(a, e0)
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let a: nat = vec_to_nat(sx);
    let e: nat = vec_to_nat(sy);
    let m: nat = vec_to_nat(sz);
    let pow: nat = pow_naive(a, e);
    let r: nat = pow % m;
    let res: Vec<char> = int_to_vec(r);
    res
}
// </vc-code>

fn main() {}
}