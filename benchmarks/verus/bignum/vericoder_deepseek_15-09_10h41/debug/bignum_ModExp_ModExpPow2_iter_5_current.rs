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
/* helper modified by LLM (iteration 5): Removed compilation errors with proper type handling */
proof fn lemma_nat_to_int_identity(n: nat)
    ensures n as int == n
{
}

proof fn lemma_nat_arithmetic()
{
}

proof fn lemma_mod_arithmetic(a: nat, b: nat, m: nat)
    requires m > 0
{
}

proof fn lemma_nat_division(n: nat, d: nat)
    requires d > 0
    ensures (n as int / d as int) as nat == n / d
{
}

proof fn lemma_nat_modulo(n: nat, d: nat)
    requires d > 0
    ensures (n as int % d as int) as nat == n % d
{
}

spec fn nat_div(a: nat, b: nat) -> nat
    requires b > 0
    ensures result == a / b
{
    a / b
}

spec fn nat_mod(a: nat, b: nat) -> nat
    requires b > 0
    ensures result == a % b
{
    a % b
}

spec fn nat_gt(a: nat, b: nat) -> bool
    ensures result == (a > b)
{
    a > b
}

spec fn nat_eq(a: nat, b: nat) -> bool
    ensures result == (a == b)
{
    a == b
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
    /* code modified by LLM (iteration 5): Fixed compilation error by using proper integer types and removing ghost block */
    let mut result: int = 1;
    let mut base: int = Str2Int(sx@) % Str2Int(sz@);
    let mut exponent: int = Str2Int(sy@);
    let z_val: int = Str2Int(sz@);
    
    while exponent > 0
        invariant
            result >= 0,
            base >= 0,
            exponent >= 0,
            Exp_int(Str2Int(sx@), Str2Int(sy@)) % z_val == (result * Exp_int(base, exponent)) % z_val
        decreases exponent
    {
        if exponent % 2 == 1 {
            result = result * base % z_val;
        }
        base = base * base % z_val;
        exponent = exponent / 2;
    }
    
    let mut res_vec = Vec::new();
    if result == 0 {
        res_vec.push('0');
    } else {
        let mut temp: int = result;
        while temp > 0
            invariant
                temp >= 0
            decreases temp
        {
            if temp % 2 == 0 {
                res_vec.push('0');
            } else {
                res_vec.push('1');
            }
            temp = temp / 2;
        }
        res_vec.reverse();
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}
