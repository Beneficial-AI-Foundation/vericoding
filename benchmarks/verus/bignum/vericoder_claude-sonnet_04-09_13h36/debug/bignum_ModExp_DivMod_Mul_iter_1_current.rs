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
lemma lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{}

lemma lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{}

lemma lemma_exp_one(x: nat)
    ensures Exp_int(x, 1) == x
{}

lemma lemma_mod_identity(x: nat, m: nat)
    requires m > 1
    ensures x % m < m
{}

spec fn Int2Str_helper(n: nat, acc: Seq<char>) -> Seq<char>
    decreases n
{
    if n == 0 {
        if acc.len() == 0 { seq!['0'] } else { acc }
    } else {
        Int2Str_helper(n / 2, seq![if n % 2 == 1 { '1' } else { '0' }] + acc)
    }
}

spec fn Int2Str(n: nat) -> Seq<char> {
    Int2Str_helper(n, Seq::<char>::empty())
}

lemma lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    lemma_int2str_helper_valid(n, Seq::<char>::empty());
}

lemma lemma_int2str_helper_valid(n: nat, acc: Seq<char>)
    requires ValidBitString(acc)
    ensures ValidBitString(Int2Str_helper(n, acc))
    decreases n
{
    if n == 0 {
        if acc.len() == 0 {
            assert(ValidBitString(seq!['0']));
        }
    } else {
        let new_acc = seq![if n % 2 == 1 { '1' } else { '0' }] + acc;
        assert(ValidBitString(new_acc));
        lemma_int2str_helper_valid(n / 2, new_acc);
    }
}

exec fn int_to_bitvec(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        proof {
            assert(result@ == seq!['0']);
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 0);
        }
        result
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        
        while temp > 0
            invariant ValidBitString(result@)
        {
            if temp % 2 == 1 {
                result.insert(0, '1');
            } else {
                result.insert(0, '0');
            }
            temp = temp / 2;
        }
        
        proof {
            lemma_int2str_valid(n);
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        proof {
            lemma_exp_zero(Str2Int(sx@));
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == 1);
            assert(1 % Str2Int(sz@) == 1);
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 1);
        }
        return result;
    }
    
    let result_val = Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@);
    let result = int_to_bitvec(result_val);
    
    proof {
        lemma_mod_identity(Exp_int(Str2Int(sx@), Str2Int(sy@)), Str2Int(sz@));
        assert(result_val < Str2Int(sz@));
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == result_val);
        assert(Str2Int(result@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    result
}
// </vc-code>

fn main() {}
}