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
proof fn exp_pow_add(x: nat, m: nat, n: nat)
  ensures Exp_int(x, m + n) == Exp_int(x, m) * Exp_int(x, n)
  decreases n
{
    if n == 0 {
        assert(Exp_int(x, m + 0) == Exp_int(x, m) * Exp_int(x, 0));
    } else {
        exp_pow_add(x, m, n - 1);
        // Exp_int(x, m + n) = Exp_int(x, m + (n-1) + 1) = Exp_int(x, m + (n-1)) * x
        assert(Exp_int(x, m + n) == Exp_int(x, m + (n - 1)) * x);
        assert(Exp_int(x, m + (n - 1)) == Exp_int(x, m) * Exp_int(x, n - 1));
        assert(Exp_int(x, m + n) == (Exp_int(x, m) * Exp_int(x, n - 1)) * x);
        assert((Exp_int(x, m) * Exp_int(x, n - 1)) * x == Exp_int(x, m) * (Exp_int(x, n - 1) * x));
        assert(Exp_int(x, n) == Exp_int(x, n - 1) * x);
        assert(Exp_int(x, m + n) == Exp_int(x, m) * Exp_int(x, n));
    }
}

proof fn exp_pow_square(x: nat, k: nat)
  ensures Exp_int(x * x, k) == Exp_int(x, k) * Exp_int(x, k)
  decreases k
{
    if k == 0 {
        assert(Exp_int(x * x, 0) == 1);
        assert(Exp_int(x, 0) * Exp_int(x, 0) == 1);
    } else {
        exp_pow_square(x, k - 1);
        // Exp_int(x * x, k) = (x * x) * Exp_int(x * x, k - 1)
        assert(Exp_int(x * x, k) == (x * x) * Exp_int(x * x, k - 1));
        // By IH, Exp_int(x * x, k - 1) == Exp_int(x, k - 1) * Exp_int(x, k - 1)
        assert(Exp_int(x * x, k - 1) == Exp_int(x, k - 1) * Exp_int(x, k - 1));
        assert((x * x) * (Exp_int(x, k - 1) * Exp_int(x, k - 1)) == (x * Exp_int(x, k - 1)) * (x * Exp_int(x, k - 1)));
        assert(x * Exp_int(x, k - 1) == Exp_int(x, k));
        assert(Exp_int(x * x, k) == Exp_int(x, k) * Exp_int(x, k));
    }
}

proof fn pow_mod_base(a: nat, m: nat, n: nat)
  ensures Exp_int(a % m, n) % m == Exp_int(a, n) % m
  decreases n
{
    if n == 0 {
        assert(Exp_int(a % m, 0) % m == 1 % m);
        assert(Exp_int(a, 0) % m == 1 % m);
    } else {
        pow_mod_base(a, m, n - 1);
        // Exp_int(a % m, n) = (a % m) * Exp_int(a % m, n-1)
        // Exp_int(a, n) = a * Exp_int(a, n-1)
        // From inductive hypothesis: Exp_int(a % m, n-1) % m == Exp_int(a, n-1) % m
        // Then ((a % m) * Exp_int(a % m, n-1)) % m == ((a % m) * Exp_int(a, n-1)) % m
        assert(( (a % m) * (Exp_int(a % m, n - 1) % m) ) % m == ( (a % m) * (Exp_int(a, n - 1) % m) ) % m);
        // reduce factors: (x % m) * y % m == (x * y) % m
        assert(( (a % m) * Exp_int(a % m, n - 1) ) % m == ( a * Exp_int(a, n - 1) ) % m);
        assert(Exp_int(a % m, n) % m == Exp_int(a, n) % m);
    }
}

exec fn slice_to_nat(s: &[char]) -> (res: nat)
  ensures res == Str2Int(s@)
  decreases s@.len()
{
    if s@.len() == 0 {
        0
    } else {
        let len_int: int = s@.len() as int;
        let last = s[(len_int - 1) as usize];
        let bit: nat = if last == '1' { 1 } else { 0 };
        let prefix = &s[..(len_int - 1) as usize];
        let prev = slice_to_nat(prefix);
        2 * prev + bit
    }
}

exec fn nat_to_bits(n: nat) -> (res: Vec<char>)
  ensures Str2Int(res@) == n
  ensures ValidBitString(res@)
  decreases n
{
    if n == 0 {
        let v = Vec::<char>::new();
        return v;
    }

    let mut pow: nat = 1;
    while pow * 2 <= n
        invariant pow >= 1;
        invariant pow <= n;
    {
        pow = pow * 2;
    }

    let mut rem: nat = n;
    let mut res: Vec<char> = Vec::new();
    while pow > 0
        invariant Str2Int(res@) + rem == n;
        invariant rem < 2 * pow;
    {
        if rem >= pow {
            res.push('1');
            rem = rem - pow;
        } else {
            res.push('0');
        }
        pow = pow / 2;
    }
    assert(rem == 0);
    assert(Str2Int(res@) == n);
    assert(forall |i: int| 0 <= i && i < res@.len() as int ==> (res@[i] == '0' || res@[i] == '1'));
    res
}

exec fn pow_mod(base0: nat, exp0: nat, modulo: nat) -> (res: nat)
  requires modulo > 1
  ensures res == Exp_int(base0, exp0) % modulo
  decreases exp0
{
    let base0_mod = base0 % modulo;
    let mut base: nat = base0_mod;
    let mut exp: nat = exp0;
    let mut acc: nat = 1;

    // invariant: (acc * Exp_int(base, exp)) % modulo == Exp_int(base0_mod, exp0) % modulo
    while exp > 0
        invariant (acc * Exp_int(base, exp)) % modulo == Exp_int(base0_mod, exp0) % modulo
        decreases exp
    {
        if exp % 2 == 1 {
            // consume one factor
            acc = (acc * base) % modulo;
            exp = exp - 1;
            // after decrement, invariant still holds
            assert((acc * Exp_int(base, exp)) % modulo == Exp_int(base0_mod, exp0) % modulo);
        }
        if exp > 0 {
            // exp is even and >= 2
            let k: nat = exp / 2;
            assert(exp == 2 * k);
            // Exp_int(base, exp) == Exp_int(base * base, k)
            // Use lemmas to justify
            exp_pow_add(base, k, k);
            exp_pow_square(base, k);
            assert(Exp_int(base, exp) == Exp_int(base * base, k));
            proof {
                pow_mod_base(base * base, modulo, k);
            }
            base = (base * base) % modulo;
            exp = k;
            assert((acc * Exp_int(base, exp)) % modulo == Exp_int(base0_mod, exp0) % modulo);
        }
    }

    // exp == 0, so invariant gives (acc * 1) % modulo == RHS
    let result = acc % modulo;
    proof {
        pow_mod_base(base0, modulo, exp0);
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base = slice_to_nat(sx);
    let exp = slice_to_nat(sy);
    let modulo = slice_to_nat(sz);
    // modulo > 1 is required by spec; use it as precondition for pow_mod
    let r = pow_mod(base, exp, modulo);
    let res_vec = nat_to_bits(r);
    res_vec
}
// </vc-code>

fn main() {}
}