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
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn pow2_lemma(n: nat)
    ensures Exp_int(2, n) > 0
    decreases n
{
    if n == 0 {
        assert(Exp_int(2, 0) == 1);
    } else {
        pow2_lemma((n - 1) as nat);
        assert(Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat));
    }
}

proof fn exp_zero_lemma(x: nat)
    ensures Exp_int(x, 0) == 1
{
    assert(Exp_int(x, 0) == 1);
}

proof fn exp_split_lemma(x: nat, a: nat, b: nat)
    ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
    decreases b
{
    if b == 0 {
        assert(Exp_int(x, a + 0) == Exp_int(x, a));
        assert(Exp_int(x, 0) == 1);
    } else {
        exp_split_lemma(x, a, (b - 1) as nat);
        assert(Exp_int(x, a + b) == x * Exp_int(x, a + (b - 1) as nat));
        assert(Exp_int(x, b) == x * Exp_int(x, (b - 1) as nat));
    }
}

proof fn exp_mod_split(base: nat, exp: nat, m: nat)
    requires m > 1,
        exp > 0
    ensures Exp_int(base, exp) % m == ((base % m) * (Exp_int(base, (exp - 1) as nat) % m)) % m
{
    assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
    assert((base * Exp_int(base, (exp - 1) as nat)) % m == ((base % m) * (Exp_int(base, (exp - 1) as nat) % m)) % m);
}
// </vc-helpers>

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
    /* code modified by LLM (iteration 6): Fix type mismatches by using nat/int literals correctly */
    let ghost y_int = Str2Int(sy@);
    let ghost z_int = Str2Int(sz@);
    let ghost x_int = Str2Int(sx@);
    
    if y_int == 0nat {
        proof {
            exp_zero_lemma(x_int);
            assert(Exp_int(x_int, 0) == 1);
        }
        let mut res = Vec::<char>::new();
        res.push('1');
        assert(Str2Int(res@) == 1);
        assert(1 % z_int < z_int);
        return res;
    }
    
    assert(y_int == Exp_int(2, n as nat));
    
    if n == 0int {
        assert(Exp_int(2, 0) == 1);
        assert(y_int == 1);
        proof {
            assert(Exp_int(x_int, 1) == x_int * Exp_int(x_int, 0));
            assert(Exp_int(x_int, 0) == 1);
            assert(Exp_int(x_int, 1) == x_int);
        }
        
        let mut result_vec = Vec::<char>::new();
        let ghost x_mod_z = x_int % z_int;
        
        if x_mod_z == 0nat {
            result_vec.push('0');
        } else {
            let ghost mut temp = x_mod_z;
            let mut digits = Vec::<char>::new();
            while temp > 0nat
                invariant
                    temp >= 0,
                    temp <= x_mod_z
                decreases temp
            {
                if temp % 2nat == 1nat {
                    digits.push('1');
                } else {
                    digits.push('0');
                }
                temp = temp / 2nat;
            }
            
            let mut i: usize = digits.len() - 1;
            while i >= 0
                invariant
                    i <= digits.len() - 1
                decreases i + 1
            {
                result_vec.push(digits[i]);
                if i == 0 {
                    break;
                }
                i = i - 1;
            }
        }
        
        return result_vec;
    }
    
    let ghost half_y = Exp_int(2, (n - 1) as nat);
    proof {
        assert(y_int == 2 * half_y);
        exp_split_lemma(x_int, half_y, half_y);
        assert(Exp_int(x_int, y_int) == Exp_int(x_int, half_y) * Exp_int(x_int, half_y));
    }
    
    let mut half_sy = Vec::<char>::new();
    half_sy.push('1');
    let mut i = 0;
    while i < n - 1int
        invariant
            0 <= i,
            i <= n - 1int,
            half_sy.len() == (i + 1) as usize
        decreases n - 1int - i
    {
        half_sy.push('0');
        i = i + 1;
    }
    
    let temp_result = ModExpPow2(sx, &half_sy, n - 1int, sz);
    proof {
        assert(Str2Int(temp_result@) == Exp_int(x_int, half_y) % z_int);
    }
    
    let squared = ModExpPow2(&temp_result, &half_sy, n - 1int, sz);
    proof {
        assert(Str2Int(squared@) == Exp_int(Str2Int(temp_result@), half_y) % z_int);
        assert(Exp_int(x_int, y_int) % z_int == (Exp_int(x_int, half_y) * Exp_int(x_int, half_y)) % z_int);
    }
    
    return squared;
}
// </vc-code>

fn main() {}
}


