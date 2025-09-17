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
proof fn lemma_exp_split(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
    // Follows directly from the definition of Exp_int
}

proof fn lemma_exp_even(x: nat, y: nat)
    requires y > 0, y % 2 == 0
    ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
    decreases y
{
    if y == 2 {
        assert(Exp_int(x, 2) == x * x * 1);
        assert(Exp_int(x * x, 1) == x * x * 1);
    } else {
        lemma_exp_split(x, y);
        lemma_exp_split(x, (y - 1) as nat);
        assert(y - 2 >= 0);
        lemma_exp_even(x, (y - 2) as nat);
    }
}

proof fn lemma_exp_odd(x: nat, y: nat)
    requires y > 0, y % 2 == 1
    ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
    decreases y
{
    if y == 1 {
        assert(Exp_int(x, 1) == x * 1);
        assert(Exp_int(x * x, 0) == 1);
    } else {
        lemma_exp_split(x, y);
        assert((y - 1) % 2 == 0);
        lemma_exp_even(x, (y - 1) as nat);
    }
}

exec fn str_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() <= 64
    ensures res as nat == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            ValidBitString(s@)
        decreases s.len() - i
    {
        let old_result = result;
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        
        assert(s@.subrange(0, (i + 1) as int) == s@.subrange(0, i as int).push(s@[i as int]));
        i = i + 1;
    }
    
    assert(s@.subrange(0, s@.len() as int) == s@);
    result
}

exec fn int_to_str(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n as nat
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    while n > 0
        invariant ValidBitString(result@)
        decreases n
    {
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    
    // Reverse the result
    let mut i: usize = 0;
    let mut j: usize = if result.len() > 0 { result.len() - 1 } else { 0 };
    
    while i < j
        invariant 
            0 <= i <= result.len(),
            0 <= j < result.len(),
            i <= j + 1,
            ValidBitString(result@)
        decreases j - i
    {
        let val_i = result[i];
        let val_j = result[j];
        result.set(i, val_j);
        result.set(j, val_i);
        i = i + 1;
        if j > 0 { j = j - 1; }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_int = str_to_int(sx);
    let y_int = str_to_int(sy);
    let z_int = str_to_int(sz);
    
    let mut result: u64 = 1;
    let mut base = x_int % z_int;
    let mut exp = y_int;
    
    while exp > 0
        invariant 
            z_int > 1,
            result < z_int,
            base < z_int,
            (result as nat * Exp_int(base as nat, exp as nat)) % (z_int as nat) == 
                Exp_int(x_int as nat, y_int as nat) % (z_int as nat)
        decreases exp
    {
        if exp % 2 == 1 {
            proof {
                lemma_exp_odd(base as nat, exp as nat);
            }
            result = (result * base) % z_int;
        } else {
            proof {
                lemma_exp_even(base as nat, exp as nat);
            }
        }
        base = (base * base) % z_int;
        exp = exp / 2;
    }
    
    assert(exp == 0);
    assert(Exp_int(base as nat, 0) == 1);
    assert(result as nat == Exp_int(x_int as nat, y_int as nat) % (z_int as nat));
    
    int_to_str(result)
}
// </vc-code>

fn main() {}
}