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
spec fn bit_val(c: char) -> nat { if c == '1' { 1 } else { 0 } }

proof fn congruence_pow(a: nat, b: nat, m: nat, k: nat)
    requires
        a % m == b % m,
    ensures
        Exp_int(a, k) % m == Exp_int(b, k) % m,
{
}

proof fn mul_mod_congruence(a: nat, b: nat, m: nat)
    ensures
        (a % m) * (b % m) % m == (a * b) % m,
{
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base: nat = Str2Int(sx@);
    let exp: nat = Str2Int(sy@);
    let modu: nat = Str2Int(sz@);
    let n: int = sy@.len() as int;

    let mut i: int = 0;
    let mut res_nat: nat = 1 % modu;
    let mut pow_nat: nat = base % modu;

    while i < n
        invariant
            0 <= i && i <= n,
            res_nat == Exp_int(base, exp % Exp_int(2, i as nat)) % modu,
            pow_nat == Exp_int(base, Exp_int(2, i as nat)) % modu,
        decreases
            (n as nat - i as nat),
    {
        let idx: int = n as int - 1 - i;
        let b: char = sy@.index(idx);
        if b == '1' {
            res_nat = (res_nat * pow_nat) % modu;
        }
        pow_nat = (pow_nat * pow_nat) % modu;
        i = i + 1;
    }

    // convert res_nat to Vec<char> in MSB-first order (so last char is LSB as required by Str2Int)
    let mut v = Vec::<char>::new();
    let mut temp: nat = res_nat;
    if temp == 0 {
        return v;
    }

    // find highest power p such that 2^p <= temp
    let mut p: int = 0;
    let mut t: nat = temp;
    while t >= 2
        invariant
            t >= 1,
        decreases
            t,
    {
        t = t / 2;
        p = p + 1;
    }

    // emit bits from p down to 0
    let mut j: int = p;
    while j >= 0
        invariant
            -1 <= j && j <= p,
        decreases
            (j as nat + 1),
    {
        let denom: nat = Exp_int(2, j as nat);
        let bit: nat = (temp / denom) % 2;
        if bit == 1 {
            v.push('1');
            temp = temp - denom;
        } else {
            v.push('0');
        }
        j = j - 1;
    }

    v
}
// </vc-code>

fn main() {}
}
