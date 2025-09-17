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
proof fn lemma_str2int_bounds(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Exp_int(2, s.len())
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(Exp_int(2, 0) == 1);
    } else {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
        assert(Str2Int(s.subrange(0, s.len() as int - 1)) < Exp_int(2, (s.len() - 1) as nat));
        if s.index(s.len() as int - 1) == '1' {
            assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 1);
            assert(Str2Int(s) < 2 * Exp_int(2, (s.len() - 1) as nat) + 1);
            assert(Str2Int(s) <= 2 * Exp_int(2, (s.len() - 1) as nat));
            assert(Str2Int(s) < Exp_int(2, s.len()));
        } else {
            assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)));
            assert(Str2Int(s) < 2 * Exp_int(2, (s.len() - 1) as nat));
            assert(Str2Int(s) < Exp_int(2, s.len()));
        }
    }
}

spec fn int_to_bitstring_spec(n: nat, len: nat) -> Seq<char>
    decreases len
{
    if len == 0 { 
        Seq::empty() 
    } else { 
        int_to_bitstring_spec(n / 2, (len - 1) as nat).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

exec fn int_to_bitstring(n: usize, len: usize) -> (res: Vec<char>)
    ensures res@ == int_to_bitstring_spec(n as nat, len as nat)
    decreases len
{
    if len == 0 {
        Vec::new()
    } else {
        let mut sub_result = int_to_bitstring(n / 2, len - 1);
        if n % 2 == 1 {
            sub_result.push('1');
        } else {
            sub_result.push('0');
        }
        sub_result
    }
}

proof fn lemma_int_to_bitstring_valid(n: nat, len: nat)
    ensures ValidBitString(int_to_bitstring_spec(n, len))
    decreases len
{
    if len == 0 {
    } else {
        lemma_int_to_bitstring_valid(n / 2, (len - 1) as nat);
    }
}

proof fn lemma_str2int_int_to_bitstring_bounded(n: nat, len: nat)
    requires n < Exp_int(2, len)
    ensures Str2Int(int_to_bitstring_spec(n, len)) == n
    decreases len
{
    if len == 0 {
        assert(n == 0);
    } else {
        lemma_str2int_int_to_bitstring_bounded(n / 2, (len - 1) as nat);
        let s = int_to_bitstring_spec(n, len);
        let sub_s = int_to_bitstring_spec(n / 2, (len - 1) as nat);
        assert(s == sub_s.push(if n % 2 == 1 { '1' } else { '0' }));
        assert(s.subrange(0, s.len() as int - 1) == sub_s);
        assert(Str2Int(s.subrange(0, s.len() as int - 1)) == n / 2);
        if n % 2 == 1 {
            assert(s.index(s.len() as int - 1) == '1');
            assert(Str2Int(s) == 2 * (n / 2) + 1);
            assert(Str2Int(s) == n);
        } else {
            assert(s.index(s.len() as int - 1) == '0');
            assert(Str2Int(s) == 2 * (n / 2) + 0);
            assert(Str2Int(s) == n);
        }
    }
}

exec fn bitstring_to_int(s: &[char]) -> (res: usize)
    requires ValidBitString(s@), s@.len() <= 64
    ensures res as nat == Str2Int(s@)
{
    let mut result: usize = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 0 <= i <= s.len(),
                  ValidBitString(s@),
                  result as nat == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        
        proof {
            let curr_subseq = s@.subrange(0, (i + 1) as int);
            let prev_subseq = s@.subrange(0, i as int);
            assert(curr_subseq == prev_subseq.push(s@[i as int]));
            assert(curr_subseq.subrange(0, curr_subseq.len() - 1) == prev_subseq);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) == s@);
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        return Vec::new();
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        return int_to_bitstring(1, 64);
    }
    
    proof {
        lemma_str2int_bounds(sx@);
        lemma_str2int_bounds(sy@);
        lemma_str2int_bounds(sz@);
    }
    
    let x = bitstring_to_int(sx);
    let z = bitstring_to_int(sz);
    
    let mut result: usize = 1;
    let mut base: usize = x % z;
    let mut i = sy.len();
    
    while i > 0
        invariant ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
                  sy@.len() > 0, Str2Int(sz@) > 1,
                  0 <= i <= sy.len(),
                  x as nat == Str2Int(sx@),
                  z as nat == Str2Int(sz@),
                  (result * Exp_int(base as nat, Str2Int(sy@.subrange(i as int, sy@.len() as int)))) % (z as int) 
                  == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
    {
        i = i - 1;
        
        if sy[i] == '1' {
            result = (result * base) % z;
        }
        base = (base * base) % z;
        
        proof {
            let curr_suffix = sy@.subrange(i as int, sy@.len() as int);
            let next_suffix = sy@.subrange((i + 1) as int, sy@.len() as int);
            assert(curr_suffix.len() == next_suffix.len() + 1);
            assert(curr_suffix[0] == sy@[i as int]);
        }
    }
    
    proof {
        assert(sy@.subrange(0, sy@.len() as int) == sy@);
        assert(Str2Int(sy@.subrange(0, sy@.len() as int)) == Str2Int(sy@));
        lemma_int_to_bitstring_valid(result as nat, 64);
        lemma_str2int_bounds(sz@);
        lemma_str2int_int_to_bitstring_bounded(result as nat, 64);
    }
    
    int_to_bitstring(result, 64)
}
// </vc-code>

fn main() {}
}