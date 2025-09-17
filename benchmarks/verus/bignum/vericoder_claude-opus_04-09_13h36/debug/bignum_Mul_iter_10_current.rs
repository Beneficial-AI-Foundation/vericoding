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
// Helper function for power of 2
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

// Helper lemmas for proving properties about Str2Int
proof fn lemma_str2int_zero(n: nat)
    ensures Str2Int(Seq::new(n, |_| '0')) == 0
    decreases n
{
    if n > 0 {
        lemma_str2int_zero((n - 1) as nat);
    }
}

proof fn lemma_str2int_shift(s: Seq<char>, n: nat)
    requires ValidBitString(s)
    ensures 
        ValidBitString(Seq::new(n, |_| '0') + s),
        Str2Int(Seq::new(n, |_| '0') + s) == Str2Int(s) * pow2(n)
    decreases n
{
    if n == 0 {
        assert(Seq::new(0, |_| '0') + s =~= s);
    } else {
        let zeros_n = Seq::new(n, |_| '0');
        let zeros_n_minus_1 = Seq::new((n - 1) as nat, |_| '0');
        lemma_str2int_shift(s, (n - 1) as nat);
        assert(zeros_n =~= Seq::new(1, |_| '0') + zeros_n_minus_1);
        assert(zeros_n + s =~= Seq::new(1, |_| '0') + (zeros_n_minus_1 + s));
    }
}

// Helper function to convert nat to binary string
exec fn nat_to_binary(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    let mut result = Vec::new();
    
    if n == 0 {
        result.push('0');
    } else {
        let mut num = n;
        let mut digits = Vec::new();
        while num > 0
            invariant 
                num <= n,
                forall |i: int| 0 <= i && i < digits@.len() ==> 
                    (digits@[i] == '0' || digits@[i] == '1')
        {
            if num % 2 == 0 {
                digits.push('0');
            } else {
                digits.push('1');
            }
            num = num / 2;
        }
        
        // Reverse the digits
        let len = digits.len();
        let mut i: usize = 0;
        while i < len 
            invariant 
                i <= len,
                result@.len() == i as int,
                forall |j: int| 0 <= j &&
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
// Helper function for power of 2
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

// Helper lemmas for proving properties about Str2Int
proof fn lemma_str2int_zero(n: nat)
    ensures Str2Int(Seq::new(n, |_| '0')) == 0
    decreases n
{
    if n > 0 {
        lemma_str2int_zero((n - 1) as nat);
    }
}

proof fn lemma_str2int_shift(s: Seq<char>, n: nat)
    requires ValidBitString(s)
    ensures 
        ValidBitString(Seq::new(n, |_| '0') + s),
        Str2Int(Seq::new(n, |_| '0') + s) == Str2Int(s) * pow2(n)
    decreases n
{
    if n == 0 {
        assert(Seq::new(0, |_| '0') + s =~= s);
    } else {
        let zeros_n = Seq::new(n, |_| '0');
        let zeros_n_minus_1 = Seq::new((n - 1) as nat, |_| '0');
        lemma_str2int_shift(s, (n - 1) as nat);
        assert(zeros_n =~= Seq::new(1, |_| '0') + zeros_n_minus_1);
        assert(zeros_n + s =~= Seq::new(1, |_| '0') + (zeros_n_minus_1 + s));
    }
}

// Helper function to convert nat to binary string
exec fn nat_to_binary(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    let mut result = Vec::new();
    
    if n == 0 {
        result.push('0');
    } else {
        let mut num = n;
        let mut digits = Vec::new();
        while num > 0
            invariant 
                num <= n,
                forall |i: int| 0 <= i && i < digits@.len() ==> 
                    (digits@[i] == '0' || digits@[i] == '1')
        {
            if num % 2 == 0 {
                digits.push('0');
            } else {
                digits.push('1');
            }
            num = num / 2;
        }
        
        // Reverse the digits
        let len = digits.len();
        let mut i: usize = 0;
        while i < len 
            invariant 
                i <= len,
                result@.len() == i as int,
                forall |j: int| 0 <= j &&
// </vc-code>

fn main() {}
}