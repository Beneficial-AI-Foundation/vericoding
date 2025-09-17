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

proof fn pow_zero_base(x: nat) 
    ensures Exp_int(0, x) == if x == 0 { 1 } else { 0 } 
{
    if x > 0 {
        pow_zero_base((x - 1) as nat);
    }
}

proof fn rec_always_decreases()
    ensures forall |x: nat, y: nat| y > 0 ==> y - 1 < y
{
}

proof fn mod_distrib(a: nat, b: nat, m: nat) 
    requires b > 1 && m > 1
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

proof fn str2int_appends(s: Seq<char>, c: char)
    requires ValidBitString(s.push(c))
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 }) 
{
    proof {
        reveal(Str2Int);
    }
}

exec fn to_vec(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@)
    ensures res@ == s@
{
    let mut v = Vec::<char>::new();
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            v@ = s@.subrange(0, i as int),
            ValidBitString(v@)
    {
        v.push(s[i]);
        i += 1;
    }
    v
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    let base = x % z;
    let mut result = 1nat % z;
    let mut power = base;
    let mut exp_remaining = y;
    
    while exp_remaining > 0
        invariant
            result == Exp_int(base, y - exp_remaining) % z,
            power == Exp_int(base, Exp_int(2, y - exp_remaining)) % z,
            exp_remaining <= y,
            result < z,
            power < z
        decreases exp_remaining
    {
        proof {
            mod_distrib(result, result, z);
            mod_distrib(power, power, z);
        }
        if exp_remaining % 2 == 1 {
            result = (result * power) % z;
        }
        power = (power * power) % z;
        exp_remaining = exp_remaining / 2;
    }
    
    proof {
        reveal(Exp_int);
        pow_zero_base(y);
    }
    
    let mut res_vec = Vec::<char>::new();
    let mut remainder = result;
    while remainder > 0
        invariant
            ValidBitString(res_vec@),
            Str2Int(res_vec@) == remainder
    {
        if remainder % 2 == 1 {
            res_vec.push('1');
        } else {
            res_vec.push('0');
        }
        remainder = remainder / 2;
    }
    res_vec.reverse();
    if res_vec.len() == 0 {
        res_vec.push('0');
    }
    res_vec
}
// </vc-code>

fn main() {}
}
