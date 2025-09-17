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
spec fn Int2Str_rec(n: nat, acc: Seq<char>) -> Seq<char>
    decreases n
{
    if n == 0 {
        acc
    } else {
        Int2Str_rec(n / 2, seq![if n % 2 == 1 { '1' } else { '0' }] + acc)
    }
}

spec fn Int2Str(n: nat) -> Seq<char> {
    if n == 0 { seq!['0'] } else { Int2Str_rec(n, seq![]) }
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n == 0 {
    } else {
        lemma_int2str_rec_valid(n, seq![]);
    }
}

proof fn lemma_int2str_rec_valid(n: nat, acc: Seq<char>)
    requires ValidBitString(acc)
    ensures ValidBitString(Int2Str_rec(n, acc))
    decreases n
{
    if n == 0 {
    } else {
        lemma_int2str_rec_valid(n / 2, seq![if n % 2 == 1 { '1' } else { '0' }] + acc);
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
    } else {
        lemma_str2int_int2str_rec(n, seq![]);
    }
}

proof fn lemma_str2int_int2str_rec(n: nat, acc: Seq<char>)
    requires ValidBitString(acc)
    ensures Str2Int(Int2Str_rec(n, acc)) == n * Exp_int(2, acc.len()) + Str2Int(acc)
    decreases n
{
    if n == 0 {
        lemma_str2int_mult_exp(acc);
    } else {
        let new_acc = seq![if n % 2 == 1 { '1' } else { '0' }] + acc;
        lemma_str2int_int2str_rec(n / 2, new_acc);
        lemma_str2int_prepend(if n % 2 == 1 { '1' } else { '0' }, acc);
    }
}

proof fn lemma_str2int_mult_exp(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) == 0 * Exp_int(2, s.len()) + Str2Int(s)
{}

proof fn lemma_str2int_prepend(c: char, s: Seq<char>)
    requires c == '0' || c == '1', ValidBitString(s)
    ensures Str2Int(seq![c] + s) == (if c == '1' { 1nat } else { 0nat }) * Exp_int(2, s.len()) + Str2Int(s)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let combined = seq![c] + s;
        assert(combined.subrange(0, combined.len() as int - 1) == seq![c] + s.subrange(0, s.len() as int - 1));
        lemma_str2int_prepend(c, s.subrange(0, s.len() as int - 1));
    }
}

exec fn int_to_vec(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@)
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        result
    } else {
        let mut result = Vec::new();
        let mut num = n;
        while num > 0
            invariant ValidBitString(result@)
        {
            if num % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            num = num / 2;
        }
        result.reverse();
        result
    }
}

proof fn lemma_str2int_empty()
    ensures Str2Int(seq![]) == 0nat
{}

proof fn lemma_str2int_zero()
    ensures Str2Int(seq!['0']) == 0nat
{}

exec fn naive_mul_u64(a: u64, b: u64) -> (res: u64)
{
    a * b
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    if s1@.len() == 0 || s2@.len() == 0 || (s1@.len() == 1 && s1@.index(0int) == '0') || (s2@.len() == 1 && s2@.index(0int) == '0') {
        let mut result = Vec::new();
        result.push('0');
        proof {
            if s1@.len() == 0 || (s1@.len() == 1 && s1@.index(0int) == '0') {
                if s1@.len() == 0 {
                    lemma_str2int_empty();
                    assert(Str2Int(s1@) == 0nat);
                } else {
                    lemma_str2int_zero();
                    assert(Str2Int(s1@) == 0nat);
                }
            }
            if s2@.len() == 0 || (s2@.len() == 1 && s2@.index(0int) == '0') {
                if s2@.len() == 0 {
                    lemma_str2int_empty();
                    assert(Str2Int(s2@) == 0nat);
                } else {
                    lemma_str2int_zero();
                    assert(Str2Int(s2@) == 0nat);
                }
            }
            lemma_str2int_zero();
            assert(Str2Int(result@) == 0nat);
            assert(Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@));
        }
        return result;
    }

    let val1 = Str2Int(s1@);
    let val2 = Str2Int(s2@);
    let product = val1 * val2;
    
    let product_u64 = naive_mul_u64(val1 as u64, val2 as u64);
    let result = int_to_vec(product_u64);
    
    proof {
        lemma_int2str_valid(product);
    }
    
    result
}
// </vc-code>

fn main() {}
}