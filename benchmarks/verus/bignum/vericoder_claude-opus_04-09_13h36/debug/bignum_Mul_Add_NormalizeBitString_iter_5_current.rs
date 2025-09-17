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
// Helper function to convert a binary string to an integer
proof fn str2int_subrange_lemma(s: Seq<char>, n: int)
    requires 
        ValidBitString(s),
        0 <= n <= s.len(),
    ensures 
        s.subrange(0, n) =~= s.take(n),
{
}

// Helper function to convert a natural number to a binary string
proof fn nat_to_binary_correct_lemma(n: nat, result: Seq<char>)
    requires
        n > 0,
        ValidBitString(result),
        result.len() >= 1,
        result.subrange(0, result.len() - 1) =~= if n / 2 == 0 { Seq::empty() } else { nat_to_binary_seq(n / 2) },
        result[result.len() - 1] == if n % 2 == 1 { '1' } else { '0' },
    ensures
        Str2Int(result) == n,
{
    let len = result.len();
    let bit = result[len - 1];
    assert(Str2Int(result) == 2 * Str2Int(result.subrange(0, len - 1)) + (if bit == '1' { 1 } else { 0 }));
    if n / 2 == 0 {
        assert(result.subrange(0, len - 1).len() == 0);
        assert(Str2Int(result.subrange(0, len - 1)) == 0);
    } else {
        assert(Str2Int(result.subrange(0, len - 1)) == n / 2);
    }
    assert(if bit == '1' { 1nat } else { 0nat } == n % 2);
    assert(n == 2 * (n / 2) + n % 2);
}

spec fn nat_to_binary_seq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        nat_to_binary_seq(n / 2).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

proof fn nat_to_binary_seq_valid(n: nat)
    ensures ValidBitString(nat_to_binary_seq(n))
    decreases n
{
    if n != 0 {
        nat_to_binary_seq_valid(n / 2);
    }
}

proof fn nat_to_binary_seq_correct(n: nat)
    ensures 
        ValidBitString(nat_to_binary_seq(n)),
        Str2Int(nat_to_binary_seq(n)) == n,
    decreases n
{
    nat_to_binary_seq_valid(n);
    if n == 0 {
        assert(nat_to_binary_seq(0) =~= Seq::empty());
        assert(Str2Int(Seq::empty()) == 0);
    } else {
        nat_to_binary_seq_correct(n / 2);
        let result = nat_to_binary_seq(n);
        let len = result.len();
        assert(len >= 1);
        assert(result[len - 1] == if n % 2 == 1 { '1' } else { '0' });
        assert(result.subrange(0, len - 1) =~= nat_to_binary_seq(n / 2));
        nat_to_binary_correct_lemma(n, result);
    }
}

// Helper to build binary string from least significant bit
spec fn build_binary_reversed(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        build_binary_reversed(n / 2).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

proof fn build_binary_reversed_correct(n: nat)
    ensures
        ValidBitString(build_binary_reversed(n)),
        Str2Int(build_binary_reversed(n)) == n,
    decreases n
{
    if n == 0 {
        assert(build_binary_reversed(0) =~= Seq::empty());
        assert(Str2Int(Seq::empty()) == 0);
    } else {
        build_binary_reversed_correct(n / 2);
        let result = build_binary_reversed(n);
        let len = result.len();
        assert(len >= 1);
        assert(result[len - 1] == if n % 2 == 1 { '1' } else { '0' });
        assert(result.subrange(0, len - 1) =~= build_binary_reversed(n / 2));
        assert(Str2Int(result) == 2 * Str2Int(result.subrange(0, len - 1)) + (if result[len - 1] == '1' { 1 } else { 0 }));
        assert(Str2Int(result.subrange(0, len - 1)) == n / 2);
        assert(n == 2 * (n / 2) + n % 2);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut n1: nat = 0;
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            n1 == Str2Int(s1@.take(i as int)),
            ValidBitString(s1@.take(i as int)),
    {
        let bit = if s1[i] == '1' { 1nat } else { 0nat };
        n1 = 2 * n1 + bit;
        
        proof {
            assert(s1@.take(i as int + 1) =~= s1@.take(i as int).push(s1@[i as int]));
            assert(Str2Int(s1@.take(i as int + 1)) == 2 * Str2Int(s1@.take(i as int)) + bit);
        }
        
        i = i + 1;
    }
    
    assert(s1@.take(s1.len() as int) =~= s1@);
    assert(n1 == Str2Int(s1@));
    
    let mut n2: nat = 0;
    let mut j: usize = 0;
    while j < s2.len()
        invariant
            0 <= j <= s2.len(),
            n2 == Str2Int(s2@.take(j as int)),
            ValidBitString(s2@.take(j as int)),
    {
        let bit = if s2[j] == '1' { 1nat } else { 0nat };
        n2 = 2 * n2 + bit;
        
        proof {
            assert(s2@.take(j as int + 1) =~= s2@.take(j as int).push(s2@[j as int]));
            assert(Str2Int(s2@.take(j as int + 1)) == 2 * Str2Int(s2@.take(j as int)) + bit);
        }
        
        j = j + 1;
    }
    
    assert(s2@.take(s2.len() as int) =~= s2@);
    assert(n2 == Str2Int(s2@));
    
    let product = n1 * n2;
    
    if product == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut n = product;
    let mut accumulated: nat = 0;
    
    while n > 0
        invariant
            ValidBitString(result@),
            n + accumulated == product,
            accumulated == Str2Int(result@.reversed()),
    {
        let bit = if n % 2 == 1 { '1' } else { '0' };
        result.push(bit);
        
        proof {
            let old_acc = accumulated;
            let old_result_rev = result@.spec_index(0, result@.len() - 1).reversed();
            assert(old_result_rev =~= result@.reversed().subrange(0, result@.len() - 1));
            assert(Str2Int(old_result_rev) == old_acc);
            
            let new_result_rev = result@.reversed();
            assert(new_result_rev.len() == result@.len());
            assert(new_result_rev[new_result_rev.len() - 1] == bit);
            assert(new_result_rev.subrange(0, new_result_rev.len() - 1) =~= old_result_rev);
            assert(Str2Int(new_result_rev) == 2 * Str2Int(old_result_rev) + (if bit == '1' { 1 } else { 0 }));
            assert(Str2Int(new_result_rev) == 2 * old_acc + (if bit == '1' { 1 } else { 0 }));
        }
        
        accumulated = 2 * accumulated + (if bit == '1' { 1 } else { 0 });
        n = n / 2;
    }
    
    assert(n == 0);
    assert(accumulated == product);
    assert(Str2Int(result@.reversed()) == product);
    
    result.reverse();
    
    assert(Str2Int(result@) == product);
    assert(Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@));
    
    return result;
}
// </vc-code>

fn main() {}
}