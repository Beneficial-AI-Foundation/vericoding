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
    assert(Str2Int(result) == 2 * Str2Int(result.subrange(0, len - 1)) + (if bit == '1' { 1nat } else { 0nat }));
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
        assert(Str2Int(result) == 2 * Str2Int(result.subrange(0, len - 1)) + (if result[len - 1] == '1' { 1nat } else { 0nat }));
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
    let mut n1: u64 = 0;
    let ghost mut n1_nat: nat = 0nat;
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            n1_nat == Str2Int(s1@.take(i as int)),
            n1 == n1_nat,
            ValidBitString(s1@.take(i as int)),
    {
        let bit: u64 = if s1[i] == '1' { 1 } else { 0 };
        n1 = 2 * n1 + bit;
        
        proof {
            let ghost bit_nat = if s1[i] == '1' { 1nat } else { 0nat };
            n1_nat = 2nat * n1_nat + bit_nat;
            assert(s1@.take(i as int + 1) =~= s1@.take(i as int).push(s1@[i as int]));
            assert(Str2Int(s1@.take(i as int + 1)) == 2 * Str2Int(s1@.take(i as int)) + bit_nat);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s1@.take(s1.len() as int) =~= s1@);
        assert(n1_nat == Str2Int(s1@));
    }
    
    let mut n2: u64 = 0;
    let ghost mut n2_nat: nat = 0nat;
    let mut j: usize = 0;
    while j < s2.len()
        invariant
            0 <= j <= s2.len(),
            n2_nat == Str2Int(s2@.take(j as int)),
            n2 == n2_nat,
            ValidBitString(s2@.take(j as int)),
    {
        let bit: u64 = if s2[j] == '1' { 1 } else { 0 };
        n2 = 2 * n2 + bit;
        
        proof {
            let ghost bit_nat = if s2[j] == '1' { 1nat } else { 0nat };
            n2_nat = 2nat * n2_nat + bit_nat;
            assert(s2@.take(j as int + 1) =~= s2@.take(j as int).push(s2@[j as int]));
            assert(Str2Int(s2@.take(j as int + 1)) == 2 * Str2Int(s2@.take(j as int)) + bit_nat);
        }
        
        j = j + 1;
    }
    
    proof {
        assert(s2@.take(s2.len() as int) =~= s2@);
        assert(n2_nat == Str2Int(s2@));
    }
    
    let product: u64 = n1 * n2;
    let ghost product_nat = n1_nat * n2_nat;
    
    proof {
        assert(product == product_nat);
    }
    
    if product == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut n: u64 = product;
    let ghost mut n_nat: nat = product_nat;
    let ghost mut accumulated: nat = 0nat;
    
    while n > 0
        invariant
            ValidBitString(result@),
            n == n_nat,
            n_nat + accumulated == product_nat,
            accumulated == Str2Int(result@.reverse()),
    {
        let bit = if n % 2 == 1 { '1' } else { '0' };
        result.push(bit);
        
        proof {
            let ghost bit_nat = if n_nat % 2nat == 1nat { 1nat } else { 0nat };
            let old_acc = accumulated;
            let old_result_rev = result@.subrange(0, result@.len() - 1).reverse();
            assert(old_result_rev =~= result@.reverse().subrange(0, result@.len() - 1));
            assert(Str2Int(old_result_rev) == old_acc);
            
            let new_result_rev = result@.reverse();
            assert(new_result_rev.len() == result@.len());
            assert(new_result_rev[new_result_rev.len() - 1] == bit);
            assert(new_result_rev.subrange(0, new_result_rev.len() - 1) =~= old_result_rev);
            assert(Str2Int(new_result_rev) == 2 * Str2Int(old_result_rev) + (if bit == '1' { 1nat } else { 0nat }));
            assert(Str2Int(new_result_rev) == 2 * old_acc + bit_nat);
            accumulated = 2nat * accumulated + bit_nat;
            n_nat = n_nat / 2nat;
        }
        
        n = n / 2;
    }
    
    proof {
        assert(n == 0);
        assert(n_nat == 0);
        assert(accumulated == product_nat);
        assert(Str2Int(result@.reverse()) == product_nat);
    }
    
    result.reverse();
    
    proof {
        assert(Str2Int(result@) == product_nat);
        assert(Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@));
    }
    
    return result;
}
// </vc-code>

fn main() {}
}