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
// <vc-helpers>
proof fn lemma_exp_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
    if b == 0 {
        // Exp_int(x, a + 0) == Exp_int(x, a)
        assert(Exp_int(x, a + b) == Exp_int(x, a));
        // Exp_int(x, 0) == 1
        assert(Exp_int(x, b) == 1);
        assert(Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b));
    } else {
        lemma_exp_add(x, a, b - 1);
        // Unfold definitions
        assert(Exp_int(x, a + b) == x * Exp_int(x, a + (b - 1)));
        assert(Exp_int(x, b) == x * Exp_int(x, b - 1));
        // Use IH: Exp_int(x, a + (b-1)) == Exp_int(x, a) * Exp_int(x, b-1)
        assert(Exp_int(x, a + (b - 1)) == Exp_int(x, a) * Exp_int(x, b - 1));
        // Multiply both sides by x
        assert(x * Exp_int(x, a + (b - 1)) == x * (Exp_int(x, a) * Exp_int(x, b - 1)));
        // Hence the desired equality
        assert(Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b));
    }
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
        // proof of correctness
        proof {
            // From recursive postcondition on old_prefix: Str2Int(old_prefix@) == n/2
            assert(Str2Int(old_prefix@) == n / 2);

            // Relate prefix@ (after push) to old_prefix@
            let t_seq = prefix@;
            let s_seq = old_prefix@;
            // lengths relation
            assert(t_seq.len() as int == s_seq.len() as int + 1);
            // the subrange of t_seq without last element equals s_seq
            assert(t_seq.subrange(0, s_seq.len() as int) == s_seq);

            // By definition of Str2Int for non-empty sequence:
            // Str2Int(t_seq) == 2 * Str2Int(t_seq.subrange(0, t_seq.len()-1)) + last_bit
            let last_bit = if b == '1' { 1 } else { 0 };
            assert(Str2Int(t_seq) == 2 * Str2Int(t_seq.subrange(0, t_seq.len() as int - 1)) + last_bit);
            // substitute subrange == s_seq
            assert(Str2Int(t_seq) == 2 * Str2Int(s_seq) + last_bit);
            // use Str2Int(old_prefix@) == n/2 to conclude Str2Int(prefix@) == n
            assert(2 * Str2Int(s_seq) + last_bit == n);
            assert(Str2Int(prefix@) == n);
        }
        return prefix;
    }
}
// </vc-helpers>
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
    let mut acc: nat = 1 % m; // =1 since m>1

    while i < n
        invariant i <= n
        invariant acc == Exp_int(x, Str2Int(sy@.subrange(0, i as int))) % m
        decreases n - i
    {
        let c = sy[i as usize];
        let bit: nat = if c == '1' { 1 } else { 0 };

        // capture acc before update to relate to invariant
        let old_acc = acc;

        // square
        acc = (acc * acc) % m;
        if bit == 1 {
            acc = (acc * base_mod) % m;
        }

        // proof that acc now equals Exp_int(x, Str2Int(sy@.subrange(0, (i+1) as int))) % m
        proof {
            let prefix_seq = sy@.subrange(0, i as int);
            let prefix_val = Str2Int(prefix_seq);
            // pre = Exp_int(x, prefix_val)
            let pre = Exp_int(x, prefix_val);

            // From invariant before the update: old_acc == pre % m
            assert(old_acc == pre % m);

            // Use lemma to relate powers:
            lemma_exp_add(x, prefix_val, prefix_val);
            assert(Exp_int(x, 2 * prefix_val) == pre * pre);

            lemma_exp_add(x, 2 * prefix_val, bit);
            assert(Exp_int(x, 2 * prefix_val + bit) == (pre * pre) * Exp_int(x, bit));

            // Exp_int(x, bit) is either 1 (bit==0) or x (bit==1)
            if bit == 0 {
                assert(Exp_int(x, bit) == 1);
            } else {
                assert(Exp_int(x, bit) == x);
            }

            // Relate modular computations:
            // old_acc == pre % m  ==> (old_acc * old_acc * (Exp_int(x,bit) % m)) % m == (pre*pre*Exp_int(x,bit)) % m
            // and acc was computed as (old_acc*old_acc*(Exp_int(x,bit)%m))%m
            // Therefore acc == Exp_int(x, 2*prefix_val + bit) % m
            assert(acc == Exp_int(x, Str2Int(sy@.subrange(0, (i + 1) as int))) % m);
        }

        i = i + 1;
    }

    // acc now equals Exp_int(x, Str2Int(sy@)) % m
    let res = nat_to_bits(acc);
    return res;
}
// </vc-code>

fn main() {}
}