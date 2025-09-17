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
            let empty: Seq<char> = seq![];
            assert(s == empty);
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
    decreases n
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
    decreases s@.len()
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
            result@ == s@.subrange(start as int, i as int)
        decreases end - i
    {
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
    if sy.len() == 0 {
        let one = vec!['1'];
        proof {
            assert(Str2Int(one@) == 1);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
        }
        let z_val = bitstring_to_int(sz);
        let result_val = 1 % z_val;
        return int_to_bitstring(result_val);
    }
    
    let x = bitstring_to_int(sx);
    let z = bitstring_to_int(sz);
    
    if sy.len() == 1 {
        if sy[0] == '0' {
            let result_val = 1 % z;
            proof {
                assert(Str2Int(sy@) == 0);
                assert(Exp_int(x as nat, 0) == 1);
            }
            return int_to_bitstring(result_val);
        } else {
            let result_val = x % z;
            proof {
                assert(Str2Int(sy@) == 1);
                assert(Exp_int(x as nat, 1) == x);
            }
            return int_to_bitstring(result_val);
        }
    }
    
    // y > 1, compute recursively
    let y_minus_1_seq = slice_subrange(sy, 0, sy.len() - 1);
    let y = bitstring_to_int(sy);
    
    proof {
        assert(y_minus_1_seq@ == sy@.subrange(0, sy@.len() as int - 1));
        assert(ValidBitString(y_minus_1_seq@));
    }
    
    let recursive_result = ModExp_DivMod(&y_minus_1_seq, &y_minus_1_seq, sz);
    let recursive_val = bitstring_to_int(&recursive_result);
    
    let x_mod = x % z;
    let result_val = (x_mod * recursive_val) % z;
    
    proof {
        lemma_exp_mod_properties(x as nat, y as nat, z as nat);
    }
    
    return int_to_bitstring(result_val);
}
// </vc-code>

fn main() {}
}