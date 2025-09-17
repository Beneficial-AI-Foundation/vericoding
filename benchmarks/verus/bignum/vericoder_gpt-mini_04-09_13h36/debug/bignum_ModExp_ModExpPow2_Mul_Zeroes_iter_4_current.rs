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
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    // This is a standard modular arithmetic property.
    assert((a * b) % m == ((a % m) * (b % m)) % m);
}

proof fn lemma_mod_mul_congruence(a: nat, b: nat, m: nat)
  requires a % m == b % m
  ensures (a * a) % m == (b * b) % m
{
    // Use lemma_mul_mod to move modulo inside products.
    lemma_mul_mod(a, a, m);
    lemma_mul_mod(b, b, m);

    let r = a % m;
    assert((a * a) % m == ((a % m) * (a % m)) % m);
    assert((b * b) % m == ((b % m) * (b % m)) % m);
    assert(a % m == r);
    assert(b % m == r);
    assert(((a % m) * (a % m)) % m == (r * r) % m);
    assert(((b % m) * (b % m)) % m == (r * r) % m);
    assert((a * a) % m == (b * b) % m);
}

exec fn nat_to_bits(n: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@)
  ensures Str2Int(res@) == n
  decreases n
{
    if n == 0 {
        return Vec::<char>::new();
    } else {
        let mut prefix = nat_to_bits(n / 2);
        let old_prefix = prefix.clone();
        let b: char = if n % 2 == 1 { '1' } else { '0' };
        prefix.push(b);
        proof {
            assert(Str2Int(old_prefix@) == n / 2);

            let t_seq = prefix@;
            let s_seq = old_prefix@;
            assert(t_seq.len() as int == s_seq.len() as int + 1);
            assert(t_seq.subrange(0, s_seq.len() as int) == s_seq);

            let last_bit = if b == '1' { 1 } else { 0 };
            assert(Str2Int(t_seq) == 2 * Str2Int(t_seq.subrange(0, t_seq.len() as int - 1)) + last_bit);
            assert(Str2Int(t_seq) == 2 * Str2Int(s_seq) + last_bit);
            assert(2 * Str2Int(s_seq) + last_bit == n);
            assert(Str2Int(prefix@) == n);
        }
        return prefix;
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
                // replace old_acc with pre % m inside modular product using lemma_mul_mod
                lemma_mul_mod(old_acc, old_acc, m);
                lemma_mul_mod(pre, pre, m);
                // since old_acc == pre % m, their squared products mod m are equal
                lemma_mod_mul_congruence(old_acc, pre, m);
                assert(acc == (pre * pre) % m);
                assert(acc == Exp_int(x, 2 * prefix_val) % m);
            } else {
                // acc was set to ((old_acc * old_acc) % m * base_mod) % m
                assert(acc == ((old_acc * old_acc) % m * base_mod) % m);

                // Replace (old_acc * old_acc) % m with (pre * pre) % m as in the bit==0 case
                lemma_mul_mod(old_acc, old_acc, m);
                lemma_mul_mod(pre, pre, m);
                lemma_mod_mul_congruence(old_acc, pre, m);
                assert((old_acc * old_acc) % m == (pre * pre) % m);

                // base_mod == x % m and Exp_int(x, bit) == x when bit==1
                assert(base_mod == x % m);
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