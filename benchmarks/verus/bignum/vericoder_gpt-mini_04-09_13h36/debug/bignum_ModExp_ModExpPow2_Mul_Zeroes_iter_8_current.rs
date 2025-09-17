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

proof fn lemma_mul_mod(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    assert((a * b) % m == ((a % m) * (b % m)) % m);
}

proof fn lemma_exp_one(x: nat)
  ensures Exp_int(x, 1) == x
{
    assert(Exp_int(x, 1) == x);
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
            // From invariant before update
            let pre = Exp_int(x, old_prefix);
            assert(old_acc == pre % m);

            // relate exponents: pre^2 * x^bit = Exp_int(x, 2*old_prefix + bit)
            lemma_exp_add(x, old_prefix, old_prefix);
            lemma_exp_add(x, 2 * old_prefix, bit);
            assert(Exp_int(x, 2 * old_prefix + bit) == (pre * pre) * Exp_int(x, bit));

            // relate Str2Int of extended prefix
            let prefix_seq = sy@.subrange(0, old_prefix.len() as int); // dummy to help types; will not be used
            // Instead, reason directly about sequence extension:
            let new_seq = sy@.subrange(0, (i + 1) as int);
            assert(new_seq.len() as int == sy@.subrange(0, i as int).len() as int + 1);
            assert(sy@.index(i as int) == c);
            let last_bit = if c == '1' { 1 } else { 0 };
            assert(Str2Int(new_seq) == 2 * Str2Int(sy@.subrange(0, i as int)) + last_bit);
            assert(last_bit == bit);

            // show acc equals the expected modular value
            if bit == 0 {
                assert(acc == (old_acc * old_acc) % m);

                // relate old_acc and pre modulo m
                assert(old_acc % m == pre % m);

                lemma_mul_mod(old_acc, old_acc, m);
                assert((old_acc * old_acc) % m == ((old_acc % m) * (old_acc % m)) % m);
                assert(((old_acc % m) * (old_acc % m)) % m == ((pre % m) * (pre % m)) % m);
                lemma_mul_mod(pre, pre, m);
                assert(((pre % m) * (pre % m)) % m == (pre * pre) % m);
                assert(acc == (pre * pre) % m);
                assert(acc == Exp_int(x, 2 * old_prefix) % m);
            } else {
                assert(acc == ((old_acc * old_acc) % m * base_mod) % m);

                assert(old_acc % m == pre % m);
                lemma_mul_mod(old_acc, old_acc, m);
                assert((old_acc * old_acc) % m == ((old_acc % m) * (old_acc % m)) % m);
                assert(((old_acc % m) * (old_acc % m)) % m == ((pre % m) * (pre % m)) % m);
                lemma_mul_mod(pre, pre, m);
                assert(((pre % m) * (pre % m)) % m == (pre * pre) % m);
                assert((old_acc * old_acc) % m == (pre * pre) % m);

                assert(base_mod == x % m);
                lemma_exp_one(x);
                assert(Exp_int(x, bit) == x);
                assert(Exp_int(x, bit) % m == base_mod);

                lemma_mul_mod(pre * pre, Exp_int(x, bit), m);
                assert(acc == (pre * pre * Exp_int(x, bit)) % m);
            }

            // tie together Str2Int and prefix update
            assert(Str2Int(sy@.subrange(0, i as int)) == old_prefix);
            assert(Str2Int(new_seq) == 2 * old_prefix + bit);
            assert(prefix == Str2Int(new_seq));
            assert(acc == Exp_int(x, Str2Int(new_seq)) % m);
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