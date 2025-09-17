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

    while i < n
        invariant i <= n
        invariant acc == Exp_int(x, Str2Int(sy@.subrange(0, i as int))) % m
        invariant acc < m
        decreases n - i
    {
        let c = sy[i as usize];
        let bit: nat = if c == '1' { 1 } else { 0 };

        let old_acc = acc;

        // square
        acc = (acc * acc) % m;
        if bit == 1 {
            acc = (acc * base_mod) % m;
        }

        proof {
            let prefix_seq = sy@.subrange(0, i as int);
            let prefix_val = Str2Int(prefix_seq);
            let pre = Exp_int(x, prefix_val);

            // from invariant before update
            assert(old_acc == pre % m);

            // relate exponents: pre^2 * x^bit = Exp_int(x, 2*prefix_val + bit)
            lemma_exp_add(x, prefix_val, prefix_val);
            lemma_exp_add(x, 2 * prefix_val, bit);
            assert(Exp_int(x, 2 * prefix_val + bit) == (pre * pre) * Exp_int(x, bit));

            // relate Str2Int of extended prefix
            let new_seq = sy@.subrange(0, (i + 1) as int);
            assert(new_seq.len() as int == prefix_seq.len() as int + 1);
            assert(new_seq.subrange(0, prefix_seq.len() as int) == prefix_seq);
            // relate runtime char c with sequence indexing
            assert(sy@.index(i as int) == c);
            assert(new_seq.index(i as int) == c);
            let last_bit = if c == '1' { 1 } else { 0 };
            assert(Str2Int(new_seq) == 2 * Str2Int(prefix_seq) + last_bit);
            assert(last_bit == bit);

            // show acc equals the expected modular value
            if bit == 0 {
                // acc was set to (old_acc * old_acc) % m
                assert(acc == (old_acc * old_acc) % m);

                // relate old_acc and pre modulo m
                assert(old_acc < m);
                assert(old_acc % m == pre % m);

                // use lemma_mul_mod to rewrite both sides
                lemma_mul_mod(old_acc, old_acc, m);
                assert((old_acc * old_acc) % m == ((old_acc % m) * (old_acc % m)) % m);

                // substitute old_acc % m == pre % m
                assert(((old_acc % m) * (old_acc % m)) % m == ((pre % m) * (pre % m)) % m);

                // use lemma_mul_mod for pre to relate to (pre * pre) % m
                lemma_mul_mod(pre, pre, m);
                assert(((pre % m) * (pre % m)) % m == (pre * pre) % m);

                // combine to get desired equality
                assert(acc == (pre * pre) % m);
                assert(acc == Exp_int(x, 2 * prefix_val) % m);
            } else {
                // acc was set to ((old_acc * old_acc) % m * base_mod) % m
                assert(acc == ((old_acc * old_acc) % m * base_mod) % m);

                // relate old_acc and pre modulo m
                assert(old_acc < m);
                assert(old_acc % m == pre % m);

                // show (old_acc * old_acc) % m == (pre * pre) % m via lemma_mul_mod and substitution
                lemma_mul_mod(old_acc, old_acc, m);
                assert((old_acc * old_acc) % m == ((old_acc % m) * (old_acc % m)) % m);
                assert(((old_acc % m) * (old_acc % m)) % m == ((pre % m) * (pre % m)) % m);
                lemma_mul_mod(pre, pre, m);
                assert(((pre % m) * (pre % m)) % m == (pre * pre) % m);
                assert((old_acc * old_acc) % m == (pre * pre) % m);

                // base_mod == x % m and Exp_int(x, bit) == x when bit==1
                assert(base_mod == x % m);
                assert(Exp_int(x, bit) == x);
                assert(Exp_int(x, bit) % m == base_mod);

                // combine to show acc == (pre*pre*Exp_int(x,bit)) % m
                lemma_mul_mod(pre * pre, Exp_int(x, bit), m);
                assert(acc == (pre * pre * Exp_int(x, bit)) % m);
            }

            assert(Str2Int(new_seq) == 2 * prefix_val + bit);
            assert(acc == Exp_int(x, Str2Int(sy@.subrange(0, (i + 1) as int))) % m);
        }

        i = i + 1;
    }

    let res = nat_to_bits(acc);
    return res;
}
// </vc-code>

fn main() {}
}