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
proof fn exp_decompose(base: nat, e: nat)
    ensures if e == 0 {
        Exp_int(base, e) == 1
    } else if e % 2 == 1 {
        Exp_int(base, e) == base * Exp_int(base * base, e / 2)
    } else {
        Exp_int(base, e) == Exp_int(base * base, e / 2)
    }
    decreases e
{
    if e == 0 {
        // Exp_int(base,0) == 1 by definition
    } else {
        // e > 0
        if e % 2 == 1 {
            // e = 2*q + 1
            let q = e / 2;
            // Exp_int(base, e) = base * Exp_int(base, e-1)
            // e-1 = 2*q
            // We can unroll one step and then show by induction
            // Use the recursive structure
            // Exp_int(base, e) = base * Exp_int(base, 2*q)
            // By repeated application, Exp_int(base, 2*q) = Exp_int(base * base, q)
            // Prove Exp_int(base, 2*q) == Exp_int(base*base, q) by induction on q
            // We'll prove it by using the definition repeatedly
            // Proceed by induction on q (which is < e)
            // Define an inner proof by recursion on q:
            fn helper(b: nat, r: nat)
                ensures Exp_int(b, 2 * r) == Exp_int(b * b, r)
                decreases r
            {
                if r == 0 {
                    // 2*r == 0, Exp_int(b,0) == 1 == Exp_int(b*b,0)
                } else {
                    // Exp_int(b, 2*r) = b * Exp_int(b, 2*r - 1)
                    // = b * (b * Exp_int(b, 2*r - 2)) = (b*b) * Exp_int(b, 2*(r-1))
                    // By IH, Exp_int(b, 2*(r-1)) == Exp_int(b*b, r-1)
                    helper(b, r - 1);
                    // then Exp_int(b, 2*r) == (b*b) * Exp_int(b*b, r-1) == Exp_int(b*b, r)
                }
            }
            helper(base, q);
            // now Exp_int(base, e) = base * Exp_int(base, 2*q) = base * Exp_int(base*base, q)
            // which matches the desired equality
        } else {
            // e even: e = 2*q
            let q = e / 2;
            // By helper above, Exp_int(base, 2*q) == Exp_int(base*base, q)
            fn helper2(b: nat, r: nat)
                ensures Exp_int(b, 2 * r) == Exp_int(b * b, r)
                decreases r
            {
                if r == 0 {
                } else {
                    helper2(b, r - 1);
                }
            }
            helper2(base, q);
            // so Exp_int(base, e) == Exp_int(base*base, e/2)
        }
    }
}

proof fn pow_mod_congruence(a: nat, b: nat, m: nat, e: nat)
    requires m > 0
    requires a % m == b % m
    ensures Exp_int(a, e) % m == Exp_int(b, e) % m
    decreases e
{
    if e == 0 {
        // Exp_int(_,0) == 1
    } else {
        // e > 0
        // Exp_int(a,e) = a * Exp_int(a,e-1)
        // Exp_int(b,e) = b * Exp_int(b,e-1)
        // By IH Exp_int(a,e-1) % m == Exp_int(b,e-1) % m
        pow_mod_congruence(a, b, m, e - 1);
        // Then a * Exp_int(a,e-1) % m == b * Exp_int(b,e-1) % m because a % m == b % m
    }
}

spec fn IntToSeq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let q = IntToSeq(n / 2);
        q + seq![ if n % 2 == 1 { '1' } else { '0' } ]
    }
}

proof fn IntToSeq_correct(n: nat)
    ensures ValidBitString(IntToSeq(n))
    ensures Str2Int(IntToSeq(n)) == n
    decreases n
{
    if n == 0 {
        // IntToSeq(0) == empty
    } else {
        IntToSeq_correct(n / 2);
        // Let q = IntToSeq(n/2)
        // IntToSeq(n) = q + [bit]
        // Str2Int(q + [bit]) = 2 * Str2Int(q) + bit
        // By IH Str2Int(q) == n/2, and bit == n%2
    }
}

// convert a slice of chars (bits) to its numeric value
exec fn seq_to_nat(s: &[char]) -> nat
{
    let mut acc: nat = 0;
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant acc == Str2Int(s@.subrange(0, i as int))
    {
        let bit = if s[i] == '1' { 1 } else { 0 };
        acc = 2 * acc + bit;
        i = i + 1;
    }
    acc
}

// produce a Vec<char> whose sequence equals IntToSeq(n)
exec fn nat_to_vec_via_inttoseq(n: nat) -> Vec<char>
{
    let s = IntToSeq(n);
    let mut v = Vec::<char>::new();
    let len = s.len();
    let mut i: usize = 0;
    while i < len
        invariant i <= len
        invariant v@ == s.subrange(0, i as int)
    {
        v.push(s.index(i as int));
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // compute numeric values of sx, sy, sz
    let nx = seq_to_nat(sx);
    let mut exp = seq_to_nat(sy);
    let m = seq_to_nat(sz);
    // modulus > 1 is given by precondition
    // reduce base modulo m
    let mut base = nx % m;
    let mut res_nat = 1 % m;
    let orig_a = nx;
    let orig_e = exp;
    // modular exponentiation loop, using binary exponentiation on exp
    while exp > 0
        invariant exp >= 0
        invariant base < m
        invariant res_nat < m
        invariant (res_nat * Exp_int(base, exp)) % m == Exp_int(orig_a, orig_e) % m
    {
        if exp % 2 == 1 {
            // res = res * base % m
            res_nat = (res_nat * base) % m;
        }
        // base = base * base % m
        base = (base * base) % m;
        exp = exp / 2;
    }
    // At this point, res_nat % m == Exp_int(orig_a, orig_e) % m.
    // Since res_nat < m, equality holds as nat.
    // convert res_nat to Vec<char> using IntToSeq
    let v = nat_to_vec_via_inttoseq(res_nat);
    return v;
}
// </vc-code>

fn main() {}
}