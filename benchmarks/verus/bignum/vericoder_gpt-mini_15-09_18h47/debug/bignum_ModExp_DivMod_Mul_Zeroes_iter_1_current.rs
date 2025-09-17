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
spec fn id_nat(n: nat) -> nat { n }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // Parse inputs to numeric nats via the provided spec function Str2Int on slices
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let m = Str2Int(sz@);

    // Fast modular exponentiation (square-and-multiply) on nats
    let mut base: nat = x % m;
    let mut exp: nat = y;
    let mut res_n: nat = 1 % m;

    while exp > 0
        invariant
            exp >= 0,
            exp <= y,
        decreases exp
    {
        if exp % 2 == 1 {
            res_n = (res_n * base) % m;
        }
        base = (base * base) % m;
        exp = exp / 2;
    }

    // Convert the resulting nat (res_n) into a Vec<char> representing its bits
    // Bits representation: most-significant bit first, least-significant bit at the end
    let mut out = Vec::<char>::new();
    if res_n == 0 {
        // empty bit-string represents 0 according to Str2Int spec
        return out;
    }

    // Collect bits least-significant-first into tmp
    let mut tmp = Vec::<char>::new();
    let mut t: nat = res_n;
    while t > 0
        invariant
            t >= 0,
            t <= res_n,
        decreases t
    {
        let b = if t % 2 == 1 { '1' } else { '0' };
        tmp.push(b);
        t = t / 2;
    }

    // Reverse tmp into out so that most-significant bit is first
    let mut i: int = tmp.len() as int;
    while i > 0
        invariant
            0 <= i && i <= tmp.len() as int,
        decreases i
    {
        i = i - 1;
        out.push(tmp.get(i));
    }

    out
}

// </vc-code>

fn main() {}
}
