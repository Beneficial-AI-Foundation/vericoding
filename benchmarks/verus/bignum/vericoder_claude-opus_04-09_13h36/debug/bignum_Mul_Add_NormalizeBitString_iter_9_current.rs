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

// Helper to compute the number of bits needed for a number
spec fn num_bits(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        1 + num_bits(n / 2)
    }
}

// Helper to get the i-th bit from the left (most significant bits first)
spec fn get_bit_at(n: nat, pos: nat, total_bits: nat) -> char
    recommends pos < total_bits
{
    let shift = total_bits - pos - 1;
    if ((n / pow2(shift)) % 2) == 1 { '1' } else { '0' }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2(n - 1)
    }
}

// Build binary string directly in correct order
spec fn build_binary_string(n: nat, bits: nat) -> Seq<char>
    decreases bits
{
    if bits == 0 {
        Seq::empty()
    } else {
        build_binary_string(n / 2, bits - 1).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

proof fn build_binary_string_valid(n: nat, bits: nat)
    ensures ValidBitString(build_binary_string(n, bits))
    decreases bits
{
    if bits != 0 {
        build_binary_string_valid(n / 2, bits - 1);
    }
}

proof fn build_binary_string_correct(n: nat, bits: nat)
    requires bits == num_bits(n) || (bits > num_bits(n) && n == 0)
    ensures
        ValidBitString(build_binary_string(n, bits)),
        Str2Int(build_binary_string(n, bits)) == n,
    decreases bits
{
    build_binary_string_valid(n, bits);
    if bits == 0 {
        assert(n == 0);
        assert(build_binary_string(0, 0) =~= Seq::empty());
        assert(Str2Int(Seq::empty()) == 0);
    } else {
        if n == 0 {
            assert(build_binary_string(0, bits) =~= build_binary_string(0, bits - 1).push('0'));
        } else {
            build_binary_string_correct(n / 2, bits - 1);
            let result = build_binary_string(n, bits);
            let len = result.len();
            assert(len == bits);
            assert(result[len - 1] == if n % 2 == 1 { '1' } else { '0' });
            assert(result.subrange(0, len - 1) =~= build_binary_string(n / 2, bits - 1));
            assert(Str2Int(result) == 2 * Str2Int(result.subrange(0, len - 1)) + (if result[len - 1] == '1' { 1nat } else { 0nat }));
            assert(n == 2 * (n / 2) + n % 2);
        }
    }
}

// Helper to compute actual bits needed
exec fn compute_num_bits(mut n: u64) -> (bits: u64)
    ensures bits == num_bits(n as nat)
{
    let mut bits = 0u64;
    let mut temp = n;
    while temp > 0
        invariant
            num_bits(n as nat) == bits + num_bits(temp as nat),
            temp <= n,
    {
        bits = bits + 1;
        temp = temp / 2;
    }
    bits
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
            let ghost bit_nat = if s1@[i as int] == '1' { 1nat } else { 0nat };
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
            let ghost bit_nat = if s2@[j as int] == '1' { 1nat } else { 0nat };
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
    
    // Compute number of bits needed
    let num_bits = compute_num_bits(product);
    
    // Build result directly in correct order
    let mut result = Vec::new();
    let mut temp = product;
    let mut stack = Vec::new();
    
    // First collect bits in reverse order
    while temp > 0
        invariant
            ValidBitString(stack@),
            temp <= product,
    {
        let bit = if temp % 2 == 1 { '1' } else { '0' };
        stack.push(bit);
        temp = temp / 2;
    }
    
    // Then build result in correct order
    let mut k = stack.len();
    while k > 0
        invariant
            0 <= k <= stack.len(),
            ValidBitString(result@),
            ValidBitString(stack@),
    {
        k = k - 1;
        result.push(stack[k]);
    }
    
    proof {
        build_binary_string_correct(product_nat, num_bits as nat);
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == product_nat);
        assert(Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@));
    }
    
    return result;
}
// </vc-code>

fn main() {}
}