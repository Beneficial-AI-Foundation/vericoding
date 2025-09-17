use vstd::prelude::*;

verus! {

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
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
// Helper function to convert a nat to a binary string
spec fn Nat2Str(n: nat) -> Seq<char>
{
    if n == 0 {
        seq!['0']
    } else {
        Nat2StrHelper(n)
    }
}

spec fn Nat2StrHelper(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        Nat2StrHelper(n / 2).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

// Proof that Nat2Str produces valid bit strings
proof fn lemma_nat2str_valid(n: nat)
    ensures ValidBitString(Nat2Str(n))
{
    if n == 0 {
        assert(ValidBitString(seq!['0']));
    } else {
        lemma_nat2str_helper_valid(n);
    }
}

proof fn lemma_nat2str_helper_valid(n: nat)
    ensures ValidBitString(Nat2StrHelper(n))
    decreases n
{
    if n > 0 {
        lemma_nat2str_helper_valid(n / 2);
    }
}

// Proof that Str2Int(Nat2Str(n)) == n
proof fn lemma_str2int_nat2str(n: nat)
    ensures Str2Int(Nat2Str(n)) == n
{
    if n == 0 {
        assert(Str2Int(seq!['0']) == 0);
    } else {
        lemma_str2int_nat2str_helper(n);
    }
}

proof fn lemma_str2int_nat2str_helper(n: nat)
    requires n > 0
    ensures Str2Int(Nat2StrHelper(n)) == n
    decreases n
{
    if n == 1 {
        assert(Nat2StrHelper(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else {
        let s = Nat2StrHelper(n);
        let s_prev = Nat2StrHelper(n / 2);
        assert(s == s_prev.push(if n % 2 == 1 { '1' } else { '0' }));
        
        if n / 2 > 0 {
            lemma_str2int_nat2str_helper(n / 2);
        }
        
        assert(s.subrange(0, s.len() as int - 1) == s_prev);
        assert(s.index(s.len() as int - 1) == if n % 2 == 1 { '1' } else { '0' });
        
        assert(Str2Int(s) == 2 * Str2Int(s_prev) + (if n % 2 == 1 { 1 } else { 0 }));
        assert(Str2Int(s) == 2 * (n / 2) + (n % 2));
        assert(2 * (n / 2) + (n % 2) == n);
    }
}

// Executive function to convert nat to binary string
exec fn nat_to_binary(n: usize) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    proof { 
        lemma_nat2str_valid(n as nat);
        lemma_str2int_nat2str(n as nat);
    }
    
    if n == 0 {
        let mut res = Vec::<char>::new();
        res.push('0');
        return res;
    }
    
    let mut res = Vec::<char>::new();
    let mut num = n;
    
    while num > 0
        invariant
            num <= n,
            res@.len() <= n,
            ValidBitString(res@),
            forall |i: int| 0 <= i && i < res@.len() ==> 
                res@.index(i) == Nat2StrHelper(n as nat).index(i)
    {
        if num % 2 == 1 {
            res.push('1');
        } else {
            res.push('0');
        }
        num = num / 2;
    }
    
    proof { 
        assert(res@ == Nat2StrHelper(n as nat));
    }
    
    res
}

// Executive function to convert binary string to nat
exec fn binary_to_nat(s: &[char]) -> (res: usize)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut result: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        
        assert(s@.subrange(0, (i + 1) as int) == 
               s@.subrange(0, i as int).push(s@.index(i as int)));
        i = i + 1;
    }
    
    assert(s@.subrange(0, s@.len() as int) == s@);
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = binary_to_nat(s1);
    let n2 = binary_to_nat(s2);
    let product = n1 * n2;
    let result = nat_to_binary(product);
    
    proof {
        assert(Str2Int(result@) == product);
        assert(product == n1 * n2);
        assert(n1 == Str2Int(s1@));
        assert(n2 == Str2Int(s2@));
        assert(Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}