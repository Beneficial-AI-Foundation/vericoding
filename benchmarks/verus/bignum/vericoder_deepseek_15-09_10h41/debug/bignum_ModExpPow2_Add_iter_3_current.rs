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

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
fn abs_diff(a: int, b: int) -> int { if a < b { b - a } else { a - b } }

proof fn exp_zero_base(x: nat) 
    ensures Exp_int(0, x) == 0 || x == 0
{
    if x > 0 {
        exp_zero_base((x - 1) as nat);
    }
}

proof fn exp_one_base(x: nat)
    ensures Exp_int(1, x) == 1
{
    if x > 0 {
        exp_one_base((x - 1) as nat);
    }
}

proof fn exp_property(x: nat, y1: nat, y2: nat)
    requires y1 <= y2
    ensures Exp_int(x, y1) <= Exp_int(x, y2) || x == 0
{
    if y1 < y2 {
        exp_property(x, y1, (y2 - 1) as nat);
    }
}

spec fn Str2Int_nonnegative(s: Seq<char>) -> bool { Str2Int(s) >= 0 }

proof fn pow2_mod_property(x: nat, n: nat, m: nat)
    requires m > 1
    ensures Exp_int(x % m, n) % m == Exp_int(x, n) % m
{
    if n > 0 {
        pow2_mod_property(x, (n - 1) as nat, m);
    }
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed syntax error and prepared for verification */
    let mut res: Vec<char> = Vec::new();
    let mut carry = 0;
    let mut i = (s1.len() as int) - 1;
    let mut j = (s2.len() as int) - 1;
    
    while i >= 0 || j >= 0 || carry > 0
        invariant
            i >= -1,
            j >= -1,
            ValidBitString(res@),
            Str2Int(res@) + Exp_int(2, (s1.len() as int - (i + 1)) as nat) * carry == Str2Int(s1.subrange((i + 1) as nat, s1.len() as nat)) + Str2Int(s2.subrange((j + 1) as nat, s2.len() as nat)),
        decreases abs_diff(i, -1) + abs_diff(j, -1) + carry
    {
        let mut sum = carry;
        
        if i >= 0 {
            sum += if s1[i as usize] == '1' { 1 } else { 0 };
            i -= 1;
        }
        
        if j >= 0 {
            sum += if s2[j as usize] == '1' { 1 } else { 0 };
            j -= 1;
        }
        
        res.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
    }
    
    if res.is_empty() {
        res.push('0');
    }
    
    res
}
// </vc-code>

fn main() {}
}


