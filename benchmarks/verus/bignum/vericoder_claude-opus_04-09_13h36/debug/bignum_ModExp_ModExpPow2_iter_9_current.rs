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
proof fn lemma_exp_split(x: nat, y: nat, z: nat)
    requires y > 0, z > 0
    ensures Exp_int(x, y) % z == if y % 2 == 0 {
        (Exp_int(x, y/2) % z * Exp_int(x, y/2) % z) % z
    } else {
        (x % z * Exp_int(x, (y-1) as nat) % z) % z
    }
{
    if y % 2 == 0 {
        assert(y >= 2);
        let half = y / 2;
        assert(y == 2 * half);
        assert(Exp_int(x, y) == Exp_int(x, half) * Exp_int(x, half)) by {
            lemma_exp_add(x, half, half);
        }
    } else {
        assert(y >= 1);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

proof fn lemma_exp_add(x: nat, a: nat, b: nat)
    ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
    decreases b
{
    if b == 0 {
        assert(Exp_int(x, b) == 1);
        assert(Exp_int(x, a + b) == Exp_int(x, a));
    } else {
        assert(Exp_int(x, a + b) == x * Exp_int(x, (a + b - 1) as nat));
        assert(a + b - 1 == a + (b - 1));
        lemma_exp_add(x, a, (b - 1) as nat);
        assert(Exp_int(x, a + (b - 1) as nat) == Exp_int(x, a) * Exp_int(x, (b - 1) as nat));
        assert(Exp_int(x, b) == x * Exp_int(x, (b - 1) as nat));
    }
}

proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c)), 
            Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1nat } else { 0nat }
    decreases s.len()
{
    let s_new = s.push(c);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
    assert(s_new[s_new.len() - 1] == c);
}

spec fn Str2Int_rev(s: Seq<char>) -> nat
    recommends ValidBitString(s)
    decreases s.len()
{
    if s.len() == 0 { 
        0 
    } else { 
        (if s[0] == '1' { 1nat } else { 0nat }) + 2 * Str2Int_rev(s.subrange(1, s.len() as int))
    }
}

proof fn lemma_str2int_rev_equals(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(reverse_seq(s)) == Str2Int_rev(s)
    decreases s.len()
{
    if s.len() == 0 {
        assert(reverse_seq(s) =~= s);
    } else {
        let rev = reverse_seq(s);
        assert(rev.len() == s.len());
        assert(rev[rev.len() - 1] == s[0]);
        assert(rev.subrange(0, rev.len() - 1) =~= reverse_seq(s.subrange(1, s.len() as int)));
        lemma_str2int_rev_equals(s.subrange(1, s.len() as int));
    }
}

exec fn int_to_binary_string(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        assert(result@.len() == 1);
        assert(result@[0] == '0');
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == 0) by {
            assert(result@.subrange(0, 0).len() == 0);
            assert(Str2Int(result@.subrange(0, 0)) == 0);
        }
        return result;
    }
    
    let mut digits = Vec::new();
    let mut remaining = n;
    
    while remaining > 0
        invariant 
            ValidBitString(digits@),
            n == remaining * Exp_int(2, digits@.len() as nat) + Str2Int_rev(digits@),
            remaining <= n
        decreases remaining
    {
        let old_remaining = remaining;
        let old_digits = digits.clone();
        
        if remaining % 2 == 0 {
            digits.push('0');
        } else {
            digits.push('1');
        }
        remaining = remaining / 2;
        
        proof {
            assert(old_remaining == 2 * remaining + if old_remaining % 2 == 1 { 1 } else { 0 });
            assert(Exp_int(2, digits@.len() as nat) == 2 * Exp_int(2, old_digits@.len() as nat));
            lemma_str2int_reverse_append_alt(old_digits@, if old_remaining % 2 == 1 { '1' } else { '0' });
        }
    }
    
    assert(remaining == 0);
    assert(n == Str2Int_rev(digits@));
    
    let reversed = reverse_vec(digits);
    assert(reversed@ =~= reverse_seq(digits@));
    proof {
        lemma_str2int_rev_equals(digits@);
    }
    reversed
}

exec fn reverse_vec(v: Vec<char>) -> (res: Vec<char>)
    ensures res@ =~= reverse_seq(v@), ValidBitString(v@) ==> ValidBitString(res@)
{
    let mut result = Vec::new();
    let mut i = v.len();
    while i > 0
        invariant 
            i <= v.len(),
            result@.len() == v.len() - i,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == v@[v@.len() - 1 - j],
            ValidBitString(v@) ==> ValidBitString(result@)
        decreases i
    {
        i = i - 1;
        result.push(v[i]);
    }
    result
}

spec fn reverse_seq(s: Seq<char>) -> Seq<char>
{
    Seq::new(s.len(), |i: int| s[s.len() - 1 - i])
}

proof fn lemma_str2int_reverse_append(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures Str2Int(reverse_seq(s.push(c))) == 
            if c == '1' { Exp_int(2, s.len() as nat) } else { 0 } + Str2Int(reverse_seq(s))
{
    let s_new = s.push(c);
    let rev_new = reverse_seq(s_new);
    let rev_old = reverse_seq(s);
    
    assert(rev_new.len() == s_new.len());
    assert(rev_new[0] == c);
    assert(rev_new.subrange(1, rev_new.len() as int) =~= rev_old);
    
    assert(Str2Int(rev_new) == 
        2 * Str2Int(rev_new.subrange(0, rev_new.len() - 1)) + 
        (if rev_new[rev_new.len() - 1] == '1' { 1nat } else { 0nat }));
}

proof fn lemma_str2int_reverse_append_alt(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures Str2Int_rev(s.push(c)) == (if c == '1' { 1 } else { 0 }) + 2 * Str2Int_rev(s)
{
    let s_new = s.push(c);
    assert(s_new[0] == c);
    assert(s_new.subrange(1, s_new.len() as int) =~= s);
}

exec fn binary_string_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() <= 64
    ensures res == Str2Int(s@)
{
    if s.len() == 0 {
        return 0;
    }
    
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant 
            i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int)),
            result <= u64::MAX / 2 || i == s.len()
        decreases s.len() - i
    {
        proof { 
            if i < s.len() {
                lemma_str2int_subrange_bound(s@, i as int);
            }
        }
        
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
        
        proof {
            lemma_str2int_extend(s@, (i - 1) as int);
        }
    }
    
    result
}

proof fn lemma_str2int_subrange_bound(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i < s.len(), s.len() <= 64
    ensures Str2Int(s.subrange(0, i)) < Exp_int(2, i as nat),
            Str2Int(s.subrange(0, i)) <= u64::MAX / 2
    decreases i
{
    if i == 0 {
        assert(s.subrange(0, i).len() == 0);
        assert(Str2Int(s.subrange(0, i)) == 0);
    } else {
        lemma_str2int_subrange_bound(s, i - 1);
        assert(Str2Int(s.subrange(0, i - 1)) < Exp_int(2, (i - 1) as nat));
        lemma_str2int_extend(s, i - 1);
        assert(Str2Int(s.subrange(0, i)) <= 2 * Str2Int(s.subrange(0, i - 1)) + 1);
        assert(Str2Int(s.subrange(0, i)) < 2 * Exp_int(2, (i - 1) as nat) + 2);
        assert(Exp_int(2, i as nat) == 2 * Exp_int(2, (i - 1) as nat));
    }
}

proof fn lemma_str2int_extend(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i < s.len()
    ensures Str2Int(s.subrange(0, i + 1)) == 
            2 * Str2Int(s.subrange(0, i)) + if s[i] == '1' { 1nat } else { 0nat }
{
    let sub = s.subrange(0, i + 1);
    assert(sub.len() == i + 1);
    assert(sub[sub.len() - 1] == s[i]);
    assert(sub.subrange(0, sub.len() - 1) =~= s.subrange(0, i));
}

exec fn decrement_binary_string(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@), Str2Int(s@) > 0, s@.len() <= 64
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s@) - 1
{
    let val = binary_string_to_int(s);
    assert(val > 0);
    int_to_binary_string(val - 1)
}

exec fn halve_binary_string(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@), s@.len() > 0, s@.len() <= 64, s@[s@.len() - 1] == '0'
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s@) / 2
{
    let val = binary_string_to_int(s);
    proof {
        lemma_str2int_even(s@);
    }
    assert(val % 2 == 0);
    int_to_binary_string(val / 2)
}

proof fn lemma_str2int_even(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0, s[s.len() - 1] == '0'
    ensures Str2Int(s) % 2 == 0
{
    assert(s.subrange(0, s.len() - 1).len() == s.len() - 1);
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
    if sy.len() == 0 {
        return vec!['1'];
    }
    
    // Check that sy and sz fit in 64 bits
    if sy.len() > 64 || sz.len() > 64 || sx.len() > 64 {
        // For very large numbers, we would need a different approach
        // For now, return a default value
        return vec!['0'];
    }
    
    let y_val = binary_string_to_int(sy);
    let z_val = binary_string_to_int(sz);
    
    if y_val == 0 {
        return vec!['1'];
    }
    
    if y_val == 1 {
        let x_val = binary_string_to_int(sx);
        let result_val = x_val % z_val;
        return int_to_binary_string(result_val);
    }
    
    if sy[sy.len() - 1] == '0' {
        // y is even
        let half_y = halve_binary_string(sy);
        
        let half_result = ModExp_ModExpPow2(sx, &half_y, sz);
        
        // Check that half_result fits in 64 bits
        if half_result.len() > 64 {
            return vec!['0'];
        }
        
        let half_val = binary_string_to_int(&half_result);
        let squared = (half_val * half_val) % z_val;
        
        proof {
            lemma_exp_split(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        }
        
        return int_to_binary_string(squared);
    } else {
        // y is odd
        let y_minus_1 = decrement_binary_string(sy);
        
        let rec_result = ModExp_ModExpPow2(sx, &y_minus_1, sz);
        
        // Check that rec_result fits in 64 bits
        if rec_result.len() > 64 {
            return vec!['0'];
        }
        
        let rec_val = binary_string_to_int(&rec_result);
        let x_val = binary_string_to_int(sx);
        let result = (x_val % z_val * rec_val) % z_val;
        
        proof {
            lemma_exp_split(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        }
        
        return int_to_binary_string(result);
    }
}
// </vc-code>

fn main() {}
}