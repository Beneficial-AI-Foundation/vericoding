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
proof fn lemma_exp_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
    if b == 0 {
        assert(Exp_int(x, a + b) == Exp_int(x, a));
        assert(Exp_int(x, b) == 1);
        assert(Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b));
    } else {
        lemma_exp_add(x, a, b - 1);
        assert(Exp_int(x, a + b) == x * Exp_int(x, a + (b - 1)));
        assert(Exp_int(x, b) == x * Exp_int(x, b - 1));
        assert(Exp_int(x, a + (b - 1)) == Exp_int(x, a) * Exp_int(x, b - 1));
        assert(x * Exp_int(x, a + (b - 1)) == x * (Exp_int(x, a) * Exp_int(x, b - 1)));
        assert(Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b));
    }
}

proof fn lemma_exp_pow2_bit(x: nat, k: nat, b: nat)
  requires b == 0 || b == 1
  ensures Exp_int(x, 2 * k + b) == Exp_int(x, k) * Exp_int(x, k) * Exp_int(x, b)
  decreases k
{
    // Exp(2k) = Exp(k) * Exp(k)
    lemma_exp_add(x, k, k);
    // Exp(2k + b) = Exp(2k) * Exp(b)
    lemma_exp_add(x, 2 * k, b);
    // combine: Exp(2k+b) = (Exp(k)*Exp(k))*Exp(b)
}

proof fn lemma_mul_mod(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    assert((a * b) % m == ((a % m) * (b % m)) % m);
}

proof fn lemma_Str2Int_extend(s: Seq<char>, i: int)
  requires ValidBitString(s)
  requires 0 <= i && i < s.len() as int
  ensures Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1 } else { 0 })
{
    // Let t = s.subrange(0, i+1). Then t.len() == i+1 > 0
    let t = s.subrange(0, i + 1);
    assert(t.len() as int == i + 1);
    // by definition of Str2Int for non-empty sequence:
    // Str2Int(t) == 2 * Str2Int(t.subrange(0, t.len()-1)) + last_bit
    assert(t.subrange(0, t.len() as int - 1) == s.subrange(0, i));
    assert(t.index(t.len() as int - 1) == s.index(i));
    if t.len() == 0 {
        // unreachable
    } else {
        assert(Str2Int(t) == 2 * Str2Int(t.subrange(0, t.len() as int - 1)) + (if t.index(t.len() as int - 1) == '1' { 1 } else { 0 }));
        assert(Str2Int(t) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1 } else { 0 }));
    }
}

proof fn lemma_exp_bit(x: nat, b: nat)
  requires b == 0 || b == 1
  ensures Exp_int(x, b) == (if b == 0 { 1 } else { x })
{
    if b == 0 {
        assert(Exp_int(x, 0) == 1);
    } else {
        // b == 1
        assert(Exp_int(x, 1) == x);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let m = Str2Int(sz@);
    let x = Str2Int(sx@);
    let base_mod = x % m;
    let n = sy.len() as nat;
    let mut i: nat = 0;
    let mut acc: nat = 1 % m;
    let mut prefix: nat = 0;

    while i < n
        invariant i <= n
        invariant acc == Exp_int(x, prefix) % m
        invariant prefix == Str2Int(sy@.subrange(0, i as int))
        invariant acc < m
        decreases n - i
    {
        let c = sy[i as usize];
        let bit: nat = if c == '1' { 1 } else { 0 };

        let old_acc = acc;
        let old_prefix = prefix;

        // square
        acc = (acc * acc) % m;
        if bit == 1 {
            acc = (acc * base_mod) % m;
        }

        // update prefix to include new bit
        prefix = 2 * old_prefix + bit;

        proof {
            // From invariants before update
            assert(old_acc == Exp_int(x, old_prefix) % m);
            assert(Str2Int(sy@.subrange(0, i as int)) == old_prefix);

            // Relate exponent: Exp(2*old_prefix + bit) = (pre*pre)*Exp(bit)
            lemma_exp_pow2_bit(x, old_prefix, bit);
            // pre = Exp(x, old_prefix)
            let pre = Exp_int(x, old_prefix);

            // Show acc equals expected modular value
            if bit == 0 {
                // acc = (old_acc * old_acc) % m
                assert(acc == (old_acc * old_acc) % m);

                // old_acc == pre % m
                assert(old_acc == pre % m);

                // (old_acc * old_acc) % m == (pre * pre) % m
                lemma_mul_mod(old_acc, old_acc, m);
                lemma_mul_mod(pre, pre, m);
                assert(((old_acc % m) * (old_acc % m)) % m == ((pre % m) * (pre % m)) % m);
                assert(acc == (pre * pre) % m);

                // combine with lemma_exp_pow2_bit (b=0): Exp(2*old_prefix) == pre*pre
                assert(acc == Exp_int(x, 2 * old_prefix) % m);
            } else {
                // bit == 1
                // acc = ((old_acc * old_acc) % m * base_mod) % m
                assert(acc == (((old_acc * old_acc) % m) * base_mod) % m);

                // old_acc == pre % m
                assert(old_acc == pre % m);

                // base_mod == x % m and Exp(x,1) == x
                assert(base_mod == x % m);
                lemma_exp_bit(x, 1);
                assert(Exp_int(x, 1) == x);
                assert(Exp_int(x, 1) % m == base_mod);

                // relate (pre*pre*Exp(1)) % m with acc
                // (old_acc*old_acc) % m == (pre*pre) % m
                lemma_mul_mod(old_acc, old_acc, m);
                lemma_mul_mod(pre, pre, m);
                assert(((old_acc % m) * (old_acc % m)) % m == ((pre % m) * (pre % m)) % m);
                assert(((old_acc * old_acc) % m) == (pre * pre) % m);

                // Now multiply by base_mod (which equals Exp(1)%m)
                lemma_mul_mod(pre * pre, Exp_int(x, 1), m);
                assert((pre * pre * Exp_int(x, 1)) % m == (((pre * pre) % m) * (Exp_int(x, 1) % m)) % m);
                assert(acc == (pre * pre * Exp_int(x, 1)) % m);

                // combine with lemma_exp_pow2_bit
                assert(acc == Exp_int(x, 2 * old_prefix + 1) % m);
            }

            // Relate Str2Int of extended prefix
            // i is in range, so we can apply lemma_Str2Int_extend for index i
            assert(0 <= i as int && i as int < sy@.len() as int);
            lemma_Str2Int_extend(sy@, i as int);
            assert(Str2Int(sy@.subrange(0, (i + 1) as int)) == 2 * Str2Int(sy@.subrange(0, i as int)) + (if sy@.index(i as int) == '1' { 1 } else { 0 }));
            assert(prefix == Str2Int(sy@.subrange(0, (i + 1) as int)));

            // Finally, tie acc to Exp_int(x, prefix) % m
            assert(acc == Exp_int(x, prefix) % m);
        }

        i = i + 1;
    }

    // At loop exit, i == n and prefix == Str2Int(sy@)
    assert(prefix == Str2Int(sy@));
    assert(acc == Exp_int(x, Str2Int(sy@)) % m);

    let res = nat_to_bits(acc);
    return res;
}
// </vc-code>

fn main() {}
}