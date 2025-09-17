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

proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_rec(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_rec(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
{
}

proof fn lemma_mod_properties(a: nat, b: nat, m: nat)
    requires m > 1
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

proof fn lemma_exp_mod(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
    decreases y
{
    if y > 0 {
        lemma_exp_rec(x, y);
        lemma_exp_mod(x, (y - 1) as nat, m);
        lemma_mod_properties(x, Exp_int(x, (y - 1) as nat), m);
    }
}

/* helper modified by LLM (iteration 2): added format_binary_number function */
fn format_binary_number(n: nat) -> Vec<char> 
    requires n >= 0
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut digits = Vec::<char>::new();
        let mut num = n;
        while num > 0
            invariant 
                num >= 0,
                ValidBitString(digits@),
                Str2Int(digits@) == n % Exp_int(2, (digits.len()) as nat)
            decreases num
        {
            if num % 2 == 1 {
                digits.push('1');
            } else {
                digits.push('0');
            }
            num = num / 2;
        }
        digits.reverse();
        digits
    }
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed implementation using format_binary_number */
{
    if sy.is_empty() {
        proof { lemma_exp_zero(Str2Int(sx@)); }
        return format_binary_number(1 % Str2Int(sz@));
    }
    
    let mut result = format_binary_number(1);
    let mut base = Str2Int(sx@) % Str2Int(sz@);
    let mut exponent = Str2Int(sy@);
    
    while exponent > 0
        invariant
            ValidBitString(result@),
            Str2Int(result@) == Exp_int(Str2Int(sx@), Str2Int(sy@) - exponent) % Str2Int(sz@),
        decreases exponent
    {
        if exponent % 2 == 1 {
            let temp = (Str2Int(result@) * base) % Str2Int(sz@);
            result = format_binary_number(temp);
        }
        base = (base * base) % Str2Int(sz@);
        exponent = exponent / 2;
    }
    
    result
}
// </vc-code>

fn main() {}
}
