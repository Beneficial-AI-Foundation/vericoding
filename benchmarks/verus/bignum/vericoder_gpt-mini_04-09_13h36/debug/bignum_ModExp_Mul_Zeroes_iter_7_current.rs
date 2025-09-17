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
exec fn slice_to_nat(s: &[char]) -> (result: nat)
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s.len()
{
    let mut i: usize = 0;
    let mut acc: nat = 0nat;
    while i < s.len()
        invariant i <= s.len() && acc == Str2Int(s@.subrange(0, i as int))
    {
        let c = s[i];
        if c == '1' {
            acc = 2nat * acc + 1nat;
        } else {
            acc = 2nat * acc;
        }
        i = i + 1;
    }
    acc
}

exec fn bits_from_nat(n: nat) -> (result: Vec<char>)
  ensures ValidBitString(result@) && Str2Int(result@) == n
  decreases n
{
    if n == 0nat {
        return Vec::<char>::new();
    }
    let mut prefix = bits_from_nat(n / 2nat);
    // capture the old sequence representation before push
    let old_seq: Seq<char> = prefix@;
    proof {
        // From recursive postcondition:
        assert(Str2Int(old_seq) == n / 2nat);
    }
    let b = if n % 2nat == 1nat { '1' } else { '0' };
    prefix.push(b);
    proof {
        let L = prefix.len() as int;
        // L > 0 because we just pushed
        assert(L > 0);
        // the prefix without the last element equals old_seq
        assert(prefix@.subrange(0, L - 1) == old_seq);
        // the last element is the bit we pushed
        assert(prefix@.index(L - 1) == b);
        // unfold definition of Str2Int for sequence of length > 0
        assert(Str2Int(prefix@) == 2nat * Str2Int(prefix@.subrange(0, L - 1)) + (if prefix@.index(L - 1) == '1' { 1nat } else { 0nat }));
        // substitute old_seq and known equalities
        assert(Str2Int(prefix@) == 2nat * Str2Int(old_seq) + (if b == '1' { 1nat } else { 0nat }));
        // arithmetic: 2*(n/2) + (n%2) == n
        assert(2nat * (n / 2nat) + (n % 2nat) == n);
        assert(Str2Int(prefix@) == n);
    }
    prefix
}

exec fn powmod_nat(x: nat, y: nat, z: nat) -> (result: nat)
  requires z > 1nat
  ensures result == Exp_int(x, y) % z
  decreases y
{
    if y == 0nat {
        return 1nat % z;
    } else {
        let ypred: nat = y - 1nat;
        let r = powmod_nat(x, ypred, z);
        let res = (x * r) % z;
        proof {
            // By induction hypothesis: r == Exp_int(x, y-1) % z
            assert(r == Exp_int(x, ypred) % z);
            // Expand Exp_int for y > 0: Exp_int(x, y) == x * Exp_int(x, ypred)
            assert(Exp_int(x, y) == x * Exp_int(x, ypred));
            // From r == Exp_int(x, ypred) % z, conclude (x * r) % z == (x * Exp_int(x, ypred)) % z
            assert((x * r) % z == (x * Exp_int(x, ypred)) % z);
            // Thus (x * r) % z == Exp_int(x, y) % z
            assert((x * r) % z == Exp_int(x, y) % z);
        }
        res
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_nat = slice_to_nat(sx);
    let y_nat = slice_to_nat(sy);
    let z_nat = slice_to_nat(sz);
    let r_nat = powmod_nat(x_nat, y_nat, z_nat);
    let res_vec = bits_from_nat(r_nat);
    res_vec
}
// </vc-code>

fn main() {}
}