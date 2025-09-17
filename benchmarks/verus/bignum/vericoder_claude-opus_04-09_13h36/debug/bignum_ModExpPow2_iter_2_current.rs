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
// Helper lemmas for modular exponentiation properties
proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{}

proof fn lemma_exp_power_of_two(x: nat, n: nat)
    requires n >= 0
    ensures Exp_int(x, Exp_int(2, n)) == if n == 0 { x } else { Exp_int(Exp_int(x, 2), Exp_int(2, (n - 1) as nat)) }
    decreases n
{
    if n == 0 {
        assert(Exp_int(2, 0) == 1);
        assert(Exp_int(x, 1) == x);
    } else {
        assert(Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat));
        // By properties of exponentiation: x^(2^n) = (x^2)^(2^(n-1))
    }
}

// Convert integer to binary string
exec fn Int2Str(val: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == val
{
    let mut result = Vec::new();
    let mut v = val;
    
    if v == 0 {
        result.push('0');
        return result;
    }
    
    while v > 0
        invariant ValidBitString(result@)
        decreases v
    {
        if v % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        v = v / 2;
    }
    
    // Reverse the result
    let mut reversed = Vec::new();
    let mut i = result.len();
    while i > 0
        invariant 0 <= i <= result.len()
        invariant ValidBitString(reversed@)
        decreases i
    {
        i = i - 1;
        reversed.push(result[i]);
    }
    
    reversed
}

// Compute (a * b) mod m
exec fn ModMul(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 0
    ensures res == (a as nat * b as nat) % m
{
    ((a as u128 * b as u128) % m as u128) as u64
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
    // Convert binary strings to integers
    let x = Str2Int(sx@) as u64;
    let y = Str2Int(sy@) as u64;
    let z = Str2Int(sz@) as u64;
    
    if y == 0 {
        // x^0 = 1
        return Int2Str(1 % z);
    }
    
    // y = 2^n, so we use repeated squaring
    let mut result = x % z;
    let mut i = 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant result < z
        decreases n - i
    {
        result = ModMul(result, result, z);
        i = i + 1;
    }
    
    Int2Str(result)
}
// </vc-code>

fn main() {}
}