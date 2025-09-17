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
spec fn Int2Str(n: nat) -> Seq<char>
decreases n
{
    if n == 0 {
        seq![]
    } else {
        Int2Str(n / 2).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n != 0 {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n || (n == 0 && Str2Int(Int2Str(n)) == 0)
    decreases n
{
    if n == 0 {
        let empty_seq: Seq<char> = seq![];
        assert(Int2Str(0) == empty_seq);
        assert(Str2Int(empty_seq) == 0);
    } else {
        lemma_str2int_int2str(n / 2);
        let s = Int2Str(n / 2);
        let c = if n % 2 == 1 { '1' } else { '0' };
        assert(Int2Str(n) == s.push(c));
        
        if n / 2 == 0 {
            assert(s == seq![]);
            assert(Int2Str(n) == seq![c]);
            if n % 2 == 1 {
                assert(Str2Int(seq!['1']) == 1);
                assert(n == 1);
            } else {
                assert(Str2Int(seq!['0']) == 0);
                assert(n == 0);
            }
        } else {
            assert(s.len() > 0);
            assert(Int2Str(n).subrange(0, Int2Str(n).len() as int - 1) == s);
            assert(Int2Str(n).index(Int2Str(n).len() as int - 1) == c);
            assert(Str2Int(Int2Str(n)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }));
            assert(Str2Int(s) == n / 2);
            assert(Str2Int(Int2Str(n)) == 2 * (n / 2) + n % 2);
            assert(2 * (n / 2) + n % 2 == n);
        }
    }
}

exec fn int_to_bitstring(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    proof { 
        lemma_int2str_valid(n as nat);
        lemma_str2int_int2str(n as nat);
    }
    
    if n == 0 {
        return Vec::new();
    }
    
    let mut result = int_to_bitstring(n / 2);
    if n % 2 == 1 {
        result.push('1');
    } else {
        result.push('0');
    }
    
    proof {
        assert(result@ == Int2Str(n as nat));
    }
    
    result
}

exec fn bitstring_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    if s.len() == 0 {
        return 0;
    }
    
    let prefix = slice_subrange(s, 0, s.len() - 1);
    let mut result = 2 * bitstring_to_int(&prefix);
    
    if s[s.len() - 1] == '1' {
        result = result + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int - 1) == prefix@);
        assert(s@.index(s@.len() as int - 1) == s[s.len() - 1]);
    }
    
    result
}

exec fn slice_subrange(s: &[char], start: usize, end: usize) -> (res: Vec<char>)
    requires start <= end <= s@.len()
    ensures res@ == s@.subrange(start as int, end as int)
{
    let mut result = Vec::new();
    let mut i = start;
    
    while i < end
        invariant
            start <= i <= end,
            result@ == s@.subrange(start as int, i as int)
    {
        result.push(s[i]);
        i = i + 1;
    }
    
    result
}

proof fn lemma_exp_properties(x: nat, y: nat)
    ensures 
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat),
        y == 0 ==> Exp_int(x, y) == 1,
        y > 1 && y % 2 == 0 ==> Exp_int(x, y) == Exp_int(x * x, y / 2),
        y > 1 && y % 2 == 1 ==> Exp_int(x, y) == x * Exp_int(x * x, y / 2)
    decreases y
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
    } else if y == 1 {
        assert(Exp_int(x, 1) == x * Exp_int(x, 0) == x * 1 == x);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        
        if y % 2 == 0 {
            // y = 2k for some k > 0
            let k = y / 2;
            assert(y == 2 * k);
            lemma_exp_even(x, k);
        } else {
            // y = 2k + 1 for some k >= 0
            let k = y / 2;
            assert(y == 2 * k + 1);
            lemma_exp_odd(x, k);
        }
    }
}

proof fn lemma_exp_even(x: nat, k: nat)
    requires k > 0
    ensures Exp_int(x, 2 * k) == Exp_int(x * x, k)
    decreases k
{
    if k == 1 {
        assert(Exp_int(x, 2) == x * Exp_int(x, 1) == x * x * Exp_int(x, 0) == x * x);
        assert(Exp_int(x * x, 1) == x * x * Exp_int(x * x, 0) == x * x);
    } else {
        assert(Exp_int(x, 2 * k) == x * Exp_int(x, (2 * k - 1) as nat));
        assert(2 * k - 1 == 2 * (k - 1) + 1);
        lemma_exp_odd(x, (k - 1) as nat);
        assert(Exp_int(x, (2 * k - 1) as nat) == x * Exp_int(x * x, (k - 1) as nat));
        assert(Exp_int(x, 2 * k) == x * x * Exp_int(x * x, (k - 1) as nat));
        assert(Exp_int(x * x, k) == (x * x) * Exp_int(x * x, (k - 1) as nat));
    }
}

proof fn lemma_exp_odd(x: nat, k: nat)
    ensures Exp_int(x, 2 * k + 1) == x * Exp_int(x * x, k)
    decreases k
{
    if k == 0 {
        assert(Exp_int(x, 1) == x * Exp_int(x, 0) == x);
        assert(Exp_int(x * x, 0) == 1);
        assert(x * Exp_int(x * x, 0) == x);
    } else {
        assert(Exp_int(x, 2 * k + 1) == x * Exp_int(x, 2 * k));
        lemma_exp_even(x, k);
        assert(Exp_int(x, 2 * k) == Exp_int(x * x, k));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let y_val = bitstring_to_int(sy);
    
    if y_val == 0 {
        proof { 
            assert(Exp_int(Str2Int(sx@), 0) == 1);
        }
        return int_to_bitstring(1);
    }
    
    let x_val = bitstring_to_int(sx);
    let z_val = bitstring_to_int(sz);
    
    if y_val == 1 {
        let res_val = x_val % z_val;
        proof {
            assert(Exp_int(Str2Int(sx@), 1) == Str2Int(sx@) * Exp_int(Str2Int(sx@), 0));
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            assert(Exp_int(Str2Int(sx@), 1) == Str2Int(sx@));
        }
        return int_to_bitstring(res_val);
    }
    
    // Binary exponentiation: if y is even, compute (x^2)^(y/2) mod z
    // if y is odd, compute x * (x^2)^(y/2) mod z
    
    let x_squared = (x_val * x_val) % z_val;
    let x_squared_str = int_to_bitstring(x_squared);
    let y_half = int_to_bitstring(y_val / 2);
    
    proof {
        lemma_exp_properties(Str2Int(sx@), Str2Int(sy@));
        assert(Str2Int(y_half@) == y_val / 2);
        assert(y_half@.len() < sy@.len()) by {
            if y_val > 1 {
                assert(y_val / 2 < y_val);
            }
        }
    }
    
    let rec_result = ModExp_DivMod(&x_squared_str, &y_half, sz);
    let rec_val = bitstring_to_int(&rec_result);
    
    let final_result = if y_val % 2 == 1 {
        (rec_val * x_val) % z_val
    } else {
        rec_val
    };
    
    proof {
        assert(Str2Int(rec_result@) == Exp_int(x_squared as nat, Str2Int(y_half@)) % Str2Int(sz@));
        assert(x_squared == (Str2Int(sx@) * Str2Int(sx@)) % Str2Int(sz@));
        
        if y_val % 2 == 1 {
            lemma_exp_properties(Str2Int(sx@), Str2Int(sy@));
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == Str2Int(sx@) * Exp_int(Str2Int(sx@) * Str2Int(sx@), Str2Int(sy@) / 2));
        } else {
            lemma_exp_properties(Str2Int(sx@), Str2Int(sy@));
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == Exp_int(Str2Int(sx@) * Str2Int(sx@), Str2Int(sy@) / 2));
        }
    }
    
    int_to_bitstring(final_result)
}
// </vc-code>

fn main() {}
}