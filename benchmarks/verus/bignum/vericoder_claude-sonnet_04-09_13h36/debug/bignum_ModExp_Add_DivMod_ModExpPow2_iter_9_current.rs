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
  if n == 0 { acc } else { Int2Str_rec(n / 2, seq![if n % 2 == 1 { '1' } else { '0' }] + acc) }
}

spec fn Int2Str(n: nat) -> Seq<char>
{
  if n == 0 { seq!['0'] } else { Int2Str_rec(n, seq![]) }
}

proof fn lemma_int2str_valid(n: nat)
  ensures ValidBitString(Int2Str(n))
  decreases n
{
  if n == 0 {
    assert(Int2Str(n) == seq!['0']);
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
    assert(Int2Str_rec(n, acc) == acc);
  } else {
    let next_acc = seq![if n % 2 == 1 { '1' } else { '0' }] + acc;
    assert(ValidBitString(next_acc));
    lemma_int2str_rec_valid(n / 2, next_acc);
  }
}

proof fn lemma_str2int_int2str(n: nat)
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 {
    assert(Int2Str(n) == seq!['0']);
    assert(Str2Int(seq!['0']) == 0);
  } else {
    lemma_str2int_int2str_rec(n, seq![], 0);
  }
}

proof fn lemma_str2int_int2str_rec(n: nat, acc: Seq<char>, acc_val: nat)
  requires ValidBitString(acc), Str2Int(acc) == acc_val
  ensures Str2Int(Int2Str_rec(n, acc)) == n * Exp_int(2, acc.len()) + acc_val
  decreases n
{
  if n == 0 {
    assert(Int2Str_rec(n, acc) == acc);
  } else {
    let bit_char = if n % 2 == 1 { '1' } else { '0' };
    let next_acc = seq![bit_char] + acc;
    lemma_str2int_int2str_rec(n / 2, next_acc, (n % 2) * Exp_int(2, acc.len()) + acc_val);
  }
}

exec fn vec_to_seq_chars(v: Vec<char>) -> (res: Seq<char>)
  ensures res == v@
{
  v@
}

exec fn int_to_bitvec(n: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@), Str2Int(res@) == n
{
  if n == 0nat {
    vec![char::try_from('0').unwrap()]
  } else {
    let mut result = Vec::new();
    let mut num = n;
    
    while num > 0nat
      invariant 
        ValidBitString(result@),
        Str2Int(result@) + num * Exp_int(2, result@.len()) == n,
        num >= 0
    {
      let bit = if num % 2 == 1nat { '1' } else { '0' };
      result.insert(0, bit);
      num = num / 2;
    }
    
    proof {
      lemma_int2str_valid(n);
      lemma_str2int_int2str(n);
    }
    
    result
  }
}

proof fn lemma_mod_exp_zero_exp(base: nat, modulus: nat)
  requires modulus > 1
  ensures Exp_int(base, 0) % modulus == 1nat % modulus
{
  assert(Exp_int(base, 0) == 1);
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  if Str2Int(sy@) == 0nat {
    proof { lemma_mod_exp_zero_exp(Str2Int(sx@), Str2Int(sz@)); }
    return int_to_bitvec(1nat % Str2Int(sz@));
  } else {
    let y_minus_one = Str2Int(sy@) - 1nat;
    let sy_minus_one = int_to_bitvec(y_minus_one);
    
    let rec_result = ModExp(sx, &sy_minus_one, sz);
    let base_mod = Str2Int(sx@) % Str2Int(sz@);
    let result_val = (base_mod * Str2Int(rec_result@)) % Str2Int(sz@);
    
    return int_to_bitvec(result_val);
  }
}
// </vc-code>

fn main() {}
}