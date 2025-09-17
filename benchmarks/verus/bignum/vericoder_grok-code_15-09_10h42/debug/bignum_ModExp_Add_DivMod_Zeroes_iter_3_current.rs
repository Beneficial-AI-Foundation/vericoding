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
/* helper modified by LLM (iteration 3): Fixed type mismatches by using int literals (e.g. 0int, 2int) */
exec fn str_to_int(s: &[char]) -> int
    requires
        ValidBitString(s@),
    ensures |result| result == Str2Int(s@) as int,
    decreases s.len()
{
    if s.len() == 0 { 0int } else {
        let hi = str_to_int(&s[0..s.len()-1]);
        let lo = if s[s.len() - 1] == '1' { 1int } else { 0int };
        hi * 2int + lo
    }
}

exec fn pow_mod(base: int, exp: int, mod_: int) -> int
    requires
        mod_ > 1int,
        exp >= 0int,
    ensures |result| result == ((Exp_int((base % mod_) as nat, exp as nat) % mod_ as nat)) as int,
    decreases exp
{
    let mut result = 1int;
    let mut b = base % mod_;
    let mut e = exp;
    while e > 0int
        invariant
            e >= 0int,
            b >= 0int && b < mod_,
            result >= 0int && result < mod_,
        decreases e
    {
        if e % 2int == 1int {
            result = (result * b) % mod_;
        }
        b = (b * b) % mod_;
        e = e / 2int;
    }
    result
}

exec fn int_to_binary(mut x: int) -> Vec<char>
    requires
        x >= 0int,
    ensures |result: Vec<char>| ValidBitString(result@),
        Str2Int(result@) == x as nat,
{
    if x == 0int {
        vec!['0']
    } else {
        let mut v = Vec::new();
        while x > 0int
        {
            let rem = x % 2int;
            v.push(if rem == 1int { '1' } else { '0' });
            x = x / 2int;
        }
        v.reverse();
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): No changes needed as errors are in helpers */
{
    let base_int = str_to_int(sx);
    let exp_int = str_to_int(sy);
    let mod_int = str_to_int(sz);
    let res_int = pow_mod(base_int, exp_int, mod_int);
    let res = int_to_binary(res_int);
    res
}
// </vc-code>

fn main() {}
}
