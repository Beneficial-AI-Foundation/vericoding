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
    let mut acc: nat = 0;
    while i < s.len()
        invariant i <= s.len() && acc == Str2Int(s@.subrange(0, i as int))
    {
        let c = s[i];
        if c == '1' {
            acc = 2 * acc + 1;
        } else {
            acc = 2 * acc;
        }
        i = i + 1;
    }
    acc
}

exec fn bits_from_nat(n: nat) -> (result: Vec<char>)
  ensures ValidBitString(result@) && Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        return Vec::<char>::new();
    }
    let mut prefix = bits_from_nat(n / 2);
    // capture the old sequence representation before push
    let old_seq: Seq<char> = prefix@;
    proof {
        // From recursive postcondition:
        assert(Str2Int(old_seq) == n / 2);
    }
    let b = if n % 2 == 1 { '1' } else { '0' };
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
        assert(Str2Int(prefix@) == 2 * Str2Int(prefix@.subrange(0, L - 1)) + (if prefix@.index(L - 1) == '1' { 1 } else { 0 }));
        // substitute old_seq and known equalities
        assert(Str2Int(prefix@) == 2 * Str2Int(old_seq) + (if b == '1' { 1 } else { 0 }));
        // arithmetic: 2*(n/2) + (n%2) == n
        assert(2 * (n / 2) + (n % 2) == n);
        assert(Str2Int(prefix@) == n);
    }
    prefix
}

exec fn powmod_nat(x: nat, y: nat, z: nat) -> (result: nat)
  requires z > 1
  ensures result == Exp_int(x, y) % z
  decreases y
{
    if y == 0 {
        return 1 % z;
    } else {
        let ypred: nat = (y - 1) as nat;
        let r = powmod_nat(x, ypred, z);
        let res = (x * r) % z;
        proof {
            // By induction hypothesis: r == Exp_int(x, y-1) % z
            // And Exp_int(x, y) == x * Exp_int(x, y-1)
            // Therefore (x * r) % z == Exp_int(x, y) % z
            assert(r == Exp_int(x, ypred) % z);
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