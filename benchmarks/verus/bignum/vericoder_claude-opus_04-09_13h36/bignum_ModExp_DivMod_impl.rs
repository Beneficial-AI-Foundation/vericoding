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
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        Int2Str(n / 2).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n > 1 {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_int2str_len_bound(n: nat)
    ensures n < 2_u64.pow(64) ==> Int2Str(n).len() <= 64
    decreases n
{
    if n >= 2 {
        lemma_int2str_len_bound(n / 2);
    }
}

proof fn lemma_str2int_bound(s: Seq<char>)
    requires ValidBitString(s), s.len() <= 64
    ensures Str2Int(s) < 2_u64.pow(64)
    decreases s.len()
{
    if s.len() > 0 {
        lemma_str2int_bound(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
        assert(Int2Str(0) == seq!['0']);
        assert(Str2Int(seq!['0']) == 0) by {
            assert(seq!['0'].len() == 1);
            let empty: Seq<char> = seq![];
            assert(seq!['0'].subrange(0, 0) == empty);
            assert(Str2Int(empty) == 0);
            assert(seq!['0'].index(0) == '0');
        }
    } else if n == 1 {
        assert(Int2Str(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1) by {
            assert(seq!['1'].len() == 1);
            let empty: Seq<char> = seq![];
            assert(seq!['1'].subrange(0, 0) == empty);
            assert(Str2Int(empty) == 0);
            assert(seq!['1'].index(0) == '1');
        }
    } else {
        lemma_str2int_int2str(n / 2);
        lemma_int2str_valid(n / 2);
        let s = Int2Str(n / 2);
        let c = if n % 2 == 1 { '1' } else { '0' };
        assert(Int2Str(n) == s.push(c));
        assert(ValidBitString(s));
        
        assert(s.len() >= 1);
        assert(Int2Str(n).subrange(0, Int2Str(n).len() as int - 1) == s);
        assert(Int2Str(n).index(Int2Str(n).len() as int - 1) == c);
        assert(Str2Int(Int2Str(n)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })) by {
            assert(ValidBitString(Int2Str(n)));
        }
        assert(Str2Int(s) == n / 2);
        assert(Str2Int(Int2Str(n)) == 2 * (n / 2) + n % 2);
        assert(2 * (n / 2) + n % 2 == n);
    }
}

exec fn int_to_bitstring(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
    decreases n
{
    proof { 
        lemma_int2str_valid(n as nat);
        lemma_str2int_int2str(n as nat);
    }
    
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        proof {
            assert(result@ == seq!['0']);
            assert(result@ == Int2Str(0));
            lemma_str2int_int2str(0);
        }
        return result;
    } else if n == 1 {
        let mut result = Vec::new();
        result.push('1');
        proof {
            assert(result@ == seq!['1']);
            assert(result@ == Int2Str(1));
            lemma_str2int_int2str(1);
        }
        return result;
    }
    
    let mut result = int_to_bitstring(n / 2);
    if n % 2 == 1 {
        result.push('1');
    } else {
        result.push('0');
    }
    
    proof {
        lemma_str2int_int2str(n as nat);
    }
    
    result
}

exec fn bitstring_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() <= 64
    ensures res == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        return 0;
    }
    
    let prefix = slice_subrange(s, 0, s.len() - 1);
    let prefix_val = bitstring_to_int(&prefix);
    
    proof {
        lemma_str2int_bound(prefix@);
        assert(prefix_val <= u64::MAX / 2);
    }
    
    let mut result = 2 * prefix_val;
    
    if s[s.len() - 1] == '1' {
        proof {
            assert(result <= u64::MAX - 1);
        }
        result = result + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int - 1) == prefix@);
    }
    
    result
}

exec fn slice_subrange(s: &[char], start: usize, end: usize) -> (res: Vec<char>)
    requires 0 <= start <= end <= s@.len()
    ensures res@ == s@.subrange(start as int, end as int)
{
    let mut result = Vec::new();
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            end <= s@.len(),
            result@ == s@.subrange(start as int, i as int),
            s@.len() == s.len()
        decreases end - i
    {
        proof {
            assert(0 <= i < s.len());
        }
        result.push(s[i]);
        i = i + 1;
    }
    result
}

proof fn lemma_exp_mod_properties(x: nat, y: nat, z: nat)
    requires z > 1, y > 0
    ensures Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
    assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    assert((x * Exp_int(x, (y - 1) as nat)) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z) by {
        lemma_mod_mul(x, Exp_int(x, (y - 1) as nat), z);
    }
}

proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    let q_a = a / m;
    let r_a = a % m;
    let q_b = b / m;
    let r_b = b % m;
    
    assert(a == q_a * m + r_a);
    assert(b == q_b * m + r_b);
    assert(a * b == (q_a * m + r_a) * (q_b * m + r_b));
    assert(a * b == q_a * q_b * m * m + q_a * m * r_b + r_a * q_b * m + r_a * r_b);
    assert((a * b) % m == (r_a * r_b) % m);
    assert((a % m) * (b % m) == r_a * r_b);
}

proof fn lemma_str2int_single_bit(c: char)
    requires c == '0' || c == '1'
    ensures Str2Int(seq![c]) == if c == '1' { 1nat } else { 0nat }
{
    assert(seq![c].len() == 1);
    let empty: Seq<char> = seq![];
    assert(seq![c].subrange(0, 0) == empty);
    assert(Str2Int(empty) == 0);
    assert(seq![c].index(0) == c);
    assert(Str2Int(seq![c]) == 2 * 0 + if c == '1' { 1nat } else { 0nat });
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
    proof {
        lemma_str2int_bound(sx@);
        lemma_str2int_bound(sy@);
        lemma_str2int_bound(sz@);
    }
    
    let x = bitstring_to_int(sx);
    let y = bitstring_to_int(sy); 
    let z = bitstring_to_int(sz);
    
    if sy.len() == 1 {
        if sy[0] == '0' {
            proof {
                lemma_str2int_single_bit('0');
                assert(sy@ == seq!['0']);
                assert(Str2Int(sy@) == 0);
                assert(Exp_int(x as nat, 0) == 1);
            }
            let result_val = 1 % z;
            return int_to_bitstring(result_val);
        } else {
            proof {
                lemma_str2int_single_bit('1');
                assert(sy@ == seq!['1']);
                assert(Str2Int(sy@) == 1);
                assert(Exp_int(x as nat, 1) == x);
            }
            let result_val = x % z;
            return int_to_bitstring(result_val);
        }
    }
    
    // y > 1, compute y/2
    let y_div_2 = y / 2;
    let y_div_2_str = int_to_bitstring(y_div_2);
    
    proof {
        lemma_int2str_len_bound(y_div_2 as nat);
    }
    
    // Recursive call: compute x^(y/2) mod z
    let recursive_result = ModExp_DivMod(sx, &y_div_2_str, sz);
    let recursive_val = bitstring_to_int(&recursive_result);
    
    // Square it: (x^(y/2))^2 mod z
    let squared = (recursive_val * recursive_val) % z;
    
    // If y is odd, multiply by x
    let result_val = if y % 2 == 1 {
        (squared * (x % z)) % z
    } else {
        squared
    };
    
    proof {
        assert(Str2Int(y_div_2_str@) == y_div_2);
        assert(recursive_val == Exp_int(x as nat, y_div_2 as nat) % (z as nat));
        
        if y % 2 == 0 {
            assert(y == 2 * y_div_2);
            assert(Exp_int(x as nat, y as nat) == Exp_int(x as nat, 2 * y_div_2 as nat));
        } else {
            assert(y == 2 * y_div_2 + 1);
            assert(Exp_int(x as nat, y as nat) == x * Exp_int(x as nat, 2 * y_div_2 as nat));
        }
    }
    
    return int_to_bitstring(result_val);
}
// </vc-code>

fn main() {}
}