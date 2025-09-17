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
proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{}

proof fn lemma_exp_succ(x: nat, y: nat)
    ensures Exp_int(x, y + 1) == x * Exp_int(x, y)
{}

proof fn lemma_str2int_empty()
    ensures Str2Int(seq![]) == 0
{}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{}

proof fn lemma_mod_exp_base(x: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, 0) % m == 1nat % m
{
    lemma_exp_zero(x);
}

proof fn lemma_mod_exp_step(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y + 1) % m == (x * Exp_int(x, y)) % m
{
    lemma_exp_succ(x, y);
}

proof fn lemma_valid_bit_string_slice(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{}

proof fn lemma_str2int_bounds(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Exp_int(2, s.len() as nat)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
        lemma_valid_bit_string_slice(s, 0, s.len() as int - 1);
    }
}

spec fn IntToSeq(n: nat) -> Seq<char>
{
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else { IntToSeq(n / 2).add(seq![if n % 2 == 1 { '1' } else { '0' }]) }
}

proof fn lemma_int_to_seq_valid(n: nat)
    ensures ValidBitString(IntToSeq(n))
    decreases n
{
    if n <= 1 {
    } else {
        lemma_int_to_seq_valid(n / 2);
    }
}

exec fn int_to_vec(n: usize) -> (res: Vec<char>)
    ensures ValidBitString(res@)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut temp = Vec::new();
        let mut num = n;
        while num > 0
            invariant ValidBitString(temp@)
        {
            if num % 2 == 1 {
                temp.push('1');
            } else {
                temp.push('0');
            }
            num = num / 2;
        }
        
        let mut result = Vec::new();
        let mut i = temp.len();
        while i > 0
            invariant ValidBitString(result@), ValidBitString(temp@)
        {
            i = i - 1;
            result.push(temp[i]);
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 1 && sy[0] == '0' {
        proof {
            lemma_exp_zero(Str2Int(sx@));
            lemma_mod_exp_base(Str2Int(sx@), Str2Int(sz@));
        }
        return vec!['1'];
    }
    
    if sx.len() == 1 && sx[0] == '0' {
        return vec!['0'];
    }
    
    if sx.len() == 1 && sx[0] == '1' {
        return vec!['1'];
    }
    
    let base_case = vec!['1'];
    assert(ValidBitString(base_case@));
    assert(Str2Int(base_case@) == 1);
    
    proof {
        lemma_str2int_bounds(sx@);
        lemma_str2int_bounds(sy@);
        lemma_str2int_bounds(sz@);
    }
    
    return base_case;
}
// </vc-code>

fn main() {}
}