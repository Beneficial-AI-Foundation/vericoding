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
        let s_prev = Nat2StrHelper(n / 2);
        let c = if n % 2 == 1 { '1' } else { '0' };
        assert(Nat2StrHelper(n) == s_prev.push(c));
        assert(c == '0' || c == '1');
        assert forall |i: int| 0 <= i && i < s_prev.len() implies #[trigger] s_prev.index(i) == '0' || s_prev.index(i) == '1';
        assert forall |i: int| 0 <= i && i < Nat2StrHelper(n).len() implies #[trigger] Nat2StrHelper(n).index(i) == '0' || Nat2StrHelper(n).index(i) == '1'
            by {
                if i < Nat2StrHelper(n).len() - 1 {
                    assert(Nat2StrHelper(n).index(i) == s_prev.index(i));
                } else if i == Nat2StrHelper(n).len() - 1 {
                    assert(Nat2StrHelper(n).index(i) == c);
                }
            }
    }
}

// Helper lemma for base cases
proof fn lemma_str2int_base_cases()
    ensures 
        Str2Int(seq![]) == 0,
        Str2Int(seq!['0']) == 0,
        Str2Int(seq!['1']) == 1
{
    // Empty sequence
    assert(seq![].len() == 0);
    assert(Str2Int(seq![]) == 0);
    
    // Single '0'
    let s0 = seq!['0'];
    assert(s0.len() == 1);
    assert(s0.subrange(0, 0) == seq![]);
    assert(s0.index(0) == '0');
    assert(Str2Int(s0) == 2 * Str2Int(seq![]) + 0);
    assert(Str2Int(s0) == 0);
    
    // Single '1'
    let s1 = seq!['1'];
    assert(s1.len() == 1);
    assert(s1.subrange(0, 0) == seq![]);
    assert(s1.index(0) == '1');
    assert(Str2Int(s1) == 2 * Str2Int(seq![]) + 1);
    assert(Str2Int(s1) == 1);
}

// Proof that Str2Int(Nat2Str(n)) == n
proof fn lemma_str2int_nat2str(n: nat)
    ensures ValidBitString(Nat2Str(n)), Str2Int(Nat2Str(n)) == n
{
    lemma_nat2str_valid(n);
    lemma_str2int_base_cases();
    
    if n == 0 {
        assert(Nat2Str(0) == seq!['0']);
    } else {
        lemma_str2int_nat2str_helper(n);
        assert(Nat2Str(n) == Nat2StrHelper(n));
    }
}

proof fn lemma_str2int_nat2str_helper(n: nat)
    requires n > 0
    ensures ValidBitString(Nat2StrHelper(n)), Str2Int(Nat2StrHelper(n)) == n
    decreases n
{
    lemma_nat2str_helper_valid(n);
    lemma_str2int_base_cases();
    
    if n == 1 {
        assert(Nat2StrHelper(1) == Nat2StrHelper(0).push('1'));
        assert(Nat2StrHelper(0) == seq![]);
        assert(Nat2StrHelper(1) == seq![].push('1'));
        assert(Nat2StrHelper(1) == seq!['1']);
    } else {
        let s = Nat2StrHelper(n);
        let s_prev = Nat2StrHelper(n / 2);
        let last_char = if n % 2 == 1 { '1' } else { '0' };
        
        assert(s == s_prev.push(last_char));
        
        if n / 2 > 0 {
            lemma_str2int_nat2str_helper(n / 2);
            assert(Str2Int(s_prev) == n / 2);
        } else {
            assert(n / 2 == 0);
            assert(s_prev == seq![]);
            assert(Str2Int(s_prev) == 0);
        }
        
        assert(s.len() > 0);
        assert(s.subrange(0, s.len() as int - 1) == s_prev);
        assert(s.index(s.len() as int - 1) == last_char);
        
        let last_val = if last_char == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(s_prev) + last_val);
        assert(Str2Int(s_prev) == n / 2);
        assert(last_val == n % 2);
        assert(2 * (n / 2) + (n % 2) == n);
        assert(Str2Int(s) == n);
    }
}

// Executive function to convert nat to binary string
exec fn nat_to_binary(n: usize) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    proof { 
        lemma_str2int_nat2str(n as nat);
    }
    
    if n == 0 {
        let mut res = Vec::<char>::new();
        res.push('0');
        
        proof {
            assert(res@ == seq!['0']);
            assert(res@ == Nat2Str(0));
        }
        
        return res;
    }
    
    let mut res = Vec::<char>::new();
    let mut num = n;
    let mut original_num = n;
    
    while num > 0
        invariant
            original_num == n,
            num <= original_num,
            ValidBitString(res@),
            forall |i: int| 0 <= i < res@.len() ==> res@[i] == Nat2StrHelper(original_num as nat)[i],
            res@.len() <= Nat2StrHelper(original_num as nat).len()
        decreases num
    {
        if num % 2 == 1 {
            res.push('1');
        } else {
            res.push('0');
        }
        num = num / 2;
    }
    
    proof {
        assert(res@.len() == Nat2StrHelper(n as nat).len());
        assert(res@ =~= Nat2StrHelper(n as nat));
    }
    
    res
}

// Executive function to convert binary string to nat
exec fn binary_to_nat(s: &[char]) -> (res: usize)
    requires ValidBitString(s@), s@.len() <= 64, Str2Int(s@) <= usize::MAX
    ensures res == Str2Int(s@)
{
    let mut result: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int)),
            result <= Str2Int(s@),
            result <= usize::MAX / 2 + 1
        decreases s.len() - i
    {
        let old_result = result;
        
        proof {
            assert(result <= usize::MAX / 2 + 1);
            assert(2 * result <= usize::MAX + 2);
            assert(2 * result <= usize::MAX);
        }
        
        result = result * 2;
        
        if s[i] == '1' {
            proof {
                assert(result + 1 <= usize::MAX);
            }
            result = result + 1;
        }
        
        proof {
            assert(ValidBitString(s@));
            assert(s@.subrange(0, (i + 1) as int).len() == (i + 1) as int);
            let prefix_with_current = s@.subrange(0, (i + 1) as int);
            let prefix = s@.subrange(0, i as int);
            assert(prefix_with_current == prefix.push(s@.index(i as int)));
            assert(prefix_with_current.subrange(0, prefix_with_current.len() as int - 1) == prefix);
            assert(prefix_with_current.index(prefix_with_current.len() as int - 1) == s@.index(i as int));
            let last_bit = if s@.index(i as int) == '1' { 1nat } else { 0nat };
            assert(ValidBitString(prefix_with_current));
            assert(Str2Int(prefix_with_current) == 2 * Str2Int(prefix) + last_bit);
            assert(old_result == Str2Int(prefix));
            assert(last_bit == if s[i] == '1' { 1nat } else { 0nat });
            assert(result == 2 * old_result + last_bit);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    
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
    proof {
        assert(ValidBitString(s1@));
        assert(ValidBitString(s2@));
    }
    
    let n1 = binary_to_nat(s1);
    let n2 = binary_to_nat(s2);
    
    proof {
        assert(n1 == Str2Int(s1@));
        assert(n2 == Str2Int(s2@));
        assert(n1 * n2 == Str2Int(s1@) * Str2Int(s2@));
    }
    
    let product: usize = n1 * n2;
    let result = nat_to_binary(product);
    
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == product);
        assert(product == Str2Int(s1@) * Str2Int(s2@));
        assert(Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}