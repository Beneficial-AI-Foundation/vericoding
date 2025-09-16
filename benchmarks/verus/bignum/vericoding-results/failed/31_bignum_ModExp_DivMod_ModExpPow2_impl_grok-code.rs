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
/* helper modified by LLM (iteration 5): fixed type mismatches by adding nat suffixes to literals like 2 and 0 */
spec fn str2nat(s: Seq<char>) -> (r: nat)
    requires ValidBitString(s)
    ensures r == Str2Int(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let sub_s = s.subrange(0, s.len() as int - 1);
        let rec = str2nat(sub_s);
        let bit = s.index(s.len() as int - 1);
        2nat * rec + if bit == '1' { 1nat } else { 0nat }
    }
}

/* helper modified by LLM (iteration 5): fixed type mismatches by adding nat suffixes to literals */
spec fn nat2str(n: nat) -> (s: Seq<char>)
    requires true
    ensures ValidBitString(s), Str2Int(s) == n
    decreases n
{
    if n == 0nat {
        Seq::<char>::empty()
    } else {
        let quot = n / 2nat;
        let rem = n % 2nat;
        let char = if rem == 0nat { '0' } else { '1' };
        nat2str(quot).push(char)
    }
}

/* helper modified by LLM (iteration 5): fixed type mismatches by adding nat suffixes to literals */
spec fn pow_mod(x: nat, y: nat, m: nat) -> (res: nat)
    requires m > 1
    ensures res == Exp_int(x, y) % m
    decreases y
{
    if y == 0nat {
        1nat % m
    } else {
        let half_pow = pow_mod(x, y / 2nat, m);
        let temp = (half_pow * half_pow) % m;
        if y % 2nat == 1nat {
            (temp * (x % m)) % m
        } else {
            temp
        }
    }
}

/* helper modified by LLM (iteration 5): fixed type mismatches in exec function by adding nat suffixes to literals */
exec fn nat2str_exec(n: nat) -> (res: Vec<char>)
    requires true
    ensures ValidBitString(res@), Str2Int(res@) == n
    decreases n
{
    let mut res = Vec::<char>::new();
    let mut current = n;
    while current > 0nat
        invariant Str2Int(res@) == n - current
        decreases current
    {
        let quot = current / 2nat;
        let rem = current % 2nat;
        let c: char = if rem == 0nat { '0' } else { '1' };
        res.insert(0, c);
        current = quot;
    }
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed as errors were in helpers */
{
    let tracked x = str2nat(sx@);
    let tracked y = str2nat(sy@);
    let tracked z = str2nat(sz@);
    let tracked r = pow_mod(x, y, z);
    let res = nat2str_exec(r);
    res
}
// </vc-code>

fn main() {}
}
