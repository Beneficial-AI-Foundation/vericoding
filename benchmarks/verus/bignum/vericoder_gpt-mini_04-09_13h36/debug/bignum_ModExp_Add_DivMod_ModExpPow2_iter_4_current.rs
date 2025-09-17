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
pub exec fn bits_to_nat(bs: &[char]) -> nat
  requires ValidBitString(bs@)
  ensures Str2Int(bs@) == result
{
    let mut acc: nat = 0;
    let mut i: usize = 0;
    while i < bs.len()
        invariant ValidBitString(bs@);
        invariant acc == Str2Int(bs@.subrange(0, i as int));
        decreases bs.len() - i;
    {
        let c = bs[i];
        if c == '1' {
            acc = 2 * acc + 1;
        } else {
            acc = 2 * acc + 0;
        }
        i = i + 1;
    }
    acc
}

pub exec fn nat_to_bits(mut n: nat) -> Vec<char>
  ensures ValidBitString(result@),
          Str2Int(result@) == old(n)
{
    if n == 0 {
        return Vec::<char>::new();
    }

    let orig = n;
    // compute highest power of two <= n
    let mut pow: nat = 1;
    while pow * 2 <= n
        invariant 1 <= pow && pow <= n + 1;
        decreases n + 1 - pow;
    {
        pow = pow * 2;
    }

    let mut out: Vec<char> = Vec::new();
    let mut cur_pow = pow;
    let mut rem = orig;

    // Invariant: orig == Str2Int(out@) * (cur_pow * 2) + rem
    // We'll loop while cur_pow > 1, and handle last bit separately.
    while cur_pow > 1
        invariant rem < cur_pow * 2;
        invariant rem >= 0;
        invariant cur_pow >= 2;
        invariant ValidBitString(out@);
        invariant orig == Str2Int(out@) * (cur_pow * 2) + rem;
        decreases cur_pow;
    {
        if rem >= cur_pow {
            out.push('1');
            rem = rem - cur_pow;
        } else {
            out.push('0');
        }
        // move to next lower power
        cur_pow = cur_pow / 2;
    }

    // Now cur_pow == 1
    if cur_pow == 1 {
        // choose last bit
        if rem >= 1 {
            out.push('1');
            rem = rem - 1;
        } else {
            out.push('0');
        }
    }

    // At this point rem must be 0 and out encodes the original number
    assert(rem == 0);
    // Prove Str2Int(out@) == orig
    assert(Str2Int(out@) == orig);

    // ValidBitString property follows from how we constructed out
    assert(forall |i: int| 0 <= i && i < out@.len() ==> (out@.index(i) == '0' || out@.index(i) == '1'));

    out
}

// Lemma: Exp_int multiplicative property
pub proof fn exp_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a + b)
  decreases b
{
    if b == 0 {
        assert(Exp_int(x, b) == 1);
        assert(Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a));
    } else {
        exp_add(x, a, b - 1);
        assert(Exp_int(x, b) == x * Exp_int(x, b - 1));
        assert(Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a + b));
    }
}

// Lemma: modular multiplication interacts with remainders
pub proof fn mod_mul_rem(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
    let qa = a / m;
    let qb = b / m;
    let ra = a % m;
    let rb = b % m;
    assert(a == m * qa + ra);
    assert(b == m * qb + rb);
    assert(a * b == m * (m * qa * qb + qa * rb + qb * ra) + ra * rb);
    assert((a * b) % m == (ra * rb) % m);
    assert(((a % m) * (b % m)) % m == (ra * rb) % m);
}

// Additional helper: Exp_int(x,1) == x (follows from definition, but we can assert)
pub proof fn exp_one(x: nat)
  ensures Exp_int(x, 1) == x
{
    assert(Exp_int(x, 1) == x * Exp_int(x, 0));
    assert(Exp_int(x, 0) == 1);
    assert(Exp_int(x, 1) == x);
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
pub exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
{
    let base: nat = bits_to_nat(sx);
    let modulus: nat = bits_to_nat(sz);
    let mut result_nat: nat = 1 % modulus;
    let n: usize = sy.len();
    let mut i: usize = 0;
    // Loop processes bits of sy from most-significant (index 0) to least-significant (index n-1)
    while i < n
        invariant 0 <= i && i <= n;
        invariant result_nat == Exp_int(base, Str2Int(sy@.subrange(0, i as int))) % modulus;
        decreases n - i;
    {
        let b: char = sy[i];
        // square step
        let tmp_sq = (result_nat * result_nat) % modulus;
        {
            let prefix_val: nat = Str2Int(sy@.subrange(0, i as int));
            assert((result_nat * result_nat) % modulus == ((Exp_int(base, prefix_val) % modulus) * (Exp_int(base, prefix_val) % modulus)) % modulus);
            mod_mul_rem(Exp_int(base, prefix_val), Exp_int(base, prefix_val), modulus);
            assert(((Exp_int(base, prefix_val) % modulus) * (Exp_int(base, prefix_val) % modulus)) % modulus == (Exp_int(base, prefix_val) * Exp_int(base, prefix_val)) % modulus);
            exp_add(base, prefix_val, prefix_val);
            assert((Exp_int(base, prefix_val) * Exp_int(base, prefix_val)) % modulus == Exp_int(base, prefix_val + prefix_val) % modulus);
            assert(tmp_sq == Exp_int(base, prefix_val + prefix_val) % modulus);
        }

        let mut tmp = tmp_sq;
        if b == '1' {
            let prefix_val: nat = Str2Int(sy@.subrange(0, i as int));
            mod_mul_rem(Exp_int(base, prefix_val + prefix_val), base, modulus);
            exp_add(base, prefix_val + prefix_val, 1);
            tmp = (tmp * (base % modulus)) % modulus;
            assert(tmp == Exp_int(base, prefix_val + prefix_val + 1) % modulus);
        }

        result_nat = tmp;
        i = i + 1;
    }

    assert(result_nat == Exp_int(base, Str2Int(sy@)) % modulus);

    let res_bits = nat_to_bits(result_nat);
    assert(ValidBitString(res_bits@));
    assert(Str2Int(res_bits@) == result_nat);
    assert(Str2Int(res_bits@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    res_bits
}
}
// </vc-code>

fn main() {}
}