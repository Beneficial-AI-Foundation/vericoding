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
        // Exp_int(x, a + 0) == Exp_int(x, a) == Exp_int(x,a) * Exp_int(x,0)
    } else {
        lemma_exp_add(x, a, b - 1);
        // Exp_int(x, a + b) == x * Exp_int(x, a + (b-1))
        // Exp_int(x, b) == x * Exp_int(x, b-1)
        // By IH: Exp_int(x, a + (b-1)) == Exp_int(x,a) * Exp_int(x, b-1)
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
        let b = if n % 2 == 1 { '1' } else { '0' };
        prefix.push(b);
        // proof of correctness
        proof {
            // From recursive postcondition: Str2Int(prefix@) == n/2
            assert(Str2Int(prefix@) == n / 2);
            // Then Str2Int(prefix@ with last bit b) == 2*(n/2) + (n%2) == n
            // Because prefix was constructed by appending the LSB.
            assert(2 * Str2Int(prefix@) + (if b == '1' { 1 } else { 0 }) == n);
            // So Str2Int(prefix@) (now includes appended bit) equals n
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
        let bit = if c == '1' { 1 } else { 0 };

        // square
        acc = (acc * acc) % m;
        if bit == 1 {
            acc = (acc * base_mod) % m;
        }

        // proof that acc now equals Exp_int(x, Str2Int(sy@.subrange(0, (i+1) as int))) % m
        proof {
            let prefix_seq = sy@.subrange(0, i as int);
            let prefix_val = Str2Int(prefix_seq);
            // From invariant: acc_before == Exp_int(x, prefix_val) % m
            // Let pre = Exp_int(x, prefix_val)
            let pre = Exp_int(x, prefix_val);

            // Exp_int(x, 2*prefix_val) == pre * pre
            lemma_exp_add(x, prefix_val, prefix_val);
            assert(Exp_int(x, 2 * prefix_val) == pre * pre);

            // Exp_int(x, 2*prefix_val + bit) == (pre * pre) * Exp_int(x, bit)
            lemma_exp_add(x, 2 * prefix_val, bit);
            assert(Exp_int(x, 2 * prefix_val + bit) == (pre * pre) * Exp_int(x, bit));

            // Exp_int(x, bit) is either 1 (bit==0) or x (bit==1)
            if bit == 0 {
                assert(Exp_int(x, bit) == 1);
            } else {
                assert(Exp_int(x, bit) == x);
            }

            // Now show the modular equality: acc (which is ((pre % m)*(pre % m)*(Exp_int(x,bit) % m)) % m)
            // equals Exp_int(x, 2*prefix_val + bit) % m
            // Use arithmetic properties of % (handled by verifier)
            // Conclude invariant for i+1:
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