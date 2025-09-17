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
    let n: int = s.len() as int;
    let mut i: int = 0;
    let mut acc: nat = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant acc == Str2Int(s@.subrange(0, i));
        decreases n - i;
    {
        let ch = s[i as usize];
        let bit: nat = if ch == '1' { 1 } else { 0 };
        let old_acc = acc;
        // update acc = 2 * old_acc + bit
        acc = old_acc * 2 + bit;
        // prove the invariant for i+1
        {
            // From the loop invariant we have old_acc == Str2Int(s@.subrange(0, i))
            assert(old_acc == Str2Int(s@.subrange(0, i)));
            // By definition of Str2Int:
            // Str2Int(s@.subrange(0, i+1)) == 2 * Str2Int(s@.subrange(0, i)) + (if s@.index(i) == '1' {1} else {0})
            // s@.index(i) corresponds to s[i as usize] which is ch, so bit matches.
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
        let old_res = res;
        let old_e = e;
        // loop condition gives old_e > 0
        assert(old_e > 0);
        // use the Exp_int lemma: a * Exp_int(a, old_e - 1) == Exp_int(a, old_e)
        assert(a * Exp_int(a, old_e - 1) == Exp_int(a, old_e));
        // perform updates
        res = old_res * a;
        e = old_e - 1;
        // from the old invariant: old_res * Exp_int(a, old_e) == Exp_int(a, e0)
        assert(old_res * Exp_int(a, old_e) == Exp_int(a, e0));
        // combine to get new invariant: res * Exp_int(a, e) == Exp_int(a, e0)
        assert(res * Exp_int(a, e) == Exp_int(a, e0));
    }
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