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

proof fn lemma_exp_successive(x: nat, n: nat)
    ensures Exp_int(x, n + 1) == x * Exp_int(x, n)
    decreases n
{
    reveal(Exp_int);
}

// Helper to convert a single digit
exec fn digit_to_char(d: u64) -> (c: char)
    requires d <= 1
    ensures c == '0' || c == '1'
    ensures (c == '1') <==> (d == 1)
    ensures (c == '0') <==> (d == 0)
{
    if d == 0 { '0' } else { '1' }
}

// Convert integer to binary string (simplified version for verification)
exec fn Int2Str(val: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures res@.len() > 0
    ensures Str2Int(res@) == val
{
    let mut result = Vec::new();
    let mut v = val;
    
    if v == 0 {
        result.push('0');
        proof {
            assert(result@.len() == 1);
            assert(result@[0] == '0');
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 0);
        }
        return result;
    }
    
    // Build the binary representation (least significant bit first)
    while v > 0
        invariant 
            forall|i: int| 0 <= i && i < result@.len() ==> 
                (result@[i] == '0' || result@[i] == '1')
        decreases v
    {
        let digit = v % 2;
        result.push(digit_to_char(digit));
        v = v / 2;
    }
    
    // Reverse the result to get most significant bit first
    let mut reversed = Vec::new();
    let mut i = result.len();
    while i > 0
        invariant 
            0 <= i <= result.len()
        invariant 
            forall|j: int| 0 <= j && j < reversed@.len() ==> 
                (reversed@[j] == '0' || reversed@[j] == '1')
        invariant reversed@.len() == result.len() - i
        decreases i
    {
        i = i - 1;
        reversed.push(result[i]);
    }
    
    proof {
        assert(reversed@.len() > 0);
        assert(ValidBitString(reversed@));
    }
    
    reversed
}

// Compute (a * b) mod m
exec fn ModMul(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 0
    ensures res < m
    ensures res == (a as nat * b as nat) % (m as nat)
{
    ((a as u128 * b as u128) % (m as u128)) as u64
}

// Helper to parse binary string to u64
exec fn parse_binary(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    requires s@.len() <= 64
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant 0 <= i <= s.len()
        invariant result == Str2Int(s@.subrange(0, i as int))
        decreases s.len() - i
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(s@ =~= s@.subrange(0, s@.len() as int));
    }
    
    result
}

// Lemma about modular exponentiation with repeated squaring
proof fn lemma_mod_exp_square(x: nat, n: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, Exp_int(2, n)) % m == 
            if n == 0 { x % m }
            else { 
                let prev = Exp_int(x, Exp_int(2, (n-1) as nat)) % m;
                (prev * prev) % m
            }
    decreases n
{
    if n == 0 {
        assert(Exp_int(2, 0) == 1);
        assert(Exp_int(x, 1) == x);
    } else {
        assert(Exp_int(2, n) == 2 * Exp_int(2, (n-1) as nat));
        assert(Exp_int(x, 2 * Exp_int(2, (n-1) as nat)) == 
               Exp_int(Exp_int(x, Exp_int(2, (n-1) as nat)), 2));
    }
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
    // Parse input strings to integers
    let x = parse_binary(sx);
    let y = parse_binary(sy); 
    let z = parse_binary(sz);
    
    proof {
        assert(x == Str2Int(sx@));
        assert(y == Str2Int(sy@));
        assert(z == Str2Int(sz@));
    }
    
    if y == 0 {
        // x^0 = 1
        proof {
            lemma_exp_zero(Str2Int(sx@));
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            assert(Str2Int(sy@) == 0);
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == 1);
        }
        let res_val = 1 % z;
        let res = Int2Str(res_val);
        proof {
            assert(Str2Int(res@) == res_val);
            assert(res_val == 1 % z);
            assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
        }
        return res;
    }
    
    // Since y = 2^n, we compute x^(2^n) mod z using repeated squaring
    // x^(2^n) = (...((x^2)^2)...)^2 (n times)
    let mut result = x % z;
    let mut i: int = 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant result < z
        invariant z > 1
        invariant result == Exp_int(x, Exp_int(2, i as nat)) % z
        decreases n - i
    {
        proof {
            lemma_mod_exp_square(x, (i + 1) as nat, z);
        }
        result = ModMul(result, result, z);
        i = i + 1;
    }
    
    proof {
        assert(i == n);
        assert(result == Exp_int(x, Exp_int(2, n as nat)) % z);
        assert(y == Exp_int(2, n as nat));
        assert(result == Exp_int(x, y) % z);
        assert(result == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    let res = Int2Str(result);
    proof {
        assert(Str2Int(res@) == result);
        assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    res
}
// </vc-code>

fn main() {}
}