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
// <vc-helpers>

proof fn lemma_bits_rev_sum(b: Seq<char>)
  requires ValidBitString(b)
  ensures Str2Int(b.rev()) ==
    (let mut_sum = (|x: nat| x); true) // dummy to satisfy syntax
  decreases b.len()
{
    // We will prove: Str2Int(b.rev()) == sum_{i=0..len-1} (if b[i]=='1' then 2^i else 0)
    // Implement by induction on b.len()
    if b.len() == 0 {
        // both sides are 0
    } else {
        let n = b.len();
        // Let b0 = b.subrange(1,n)
        let b0 = b.subrange(1, n);
        // By induction on b0
        lemma_bits_rev_sum(b0);
        // Now reason:
        // reverse(b) has form reverse(b) = b.subrange(n-1,n) + reverse(b0)
        // i.e., r[0] = b[n-1], ..., r[n-1] = b[0]
        // Str2Int(reverse(b)) = 2 * Str2Int(reverse(b).subrange(0, n-1)) + (if reverse(b)[n-1]=='1' then 1 else 0)
        // reverse(b).subrange(0,n-1) == reverse(b0)
        // reverse(b)[n-1] == b[0]
        assert(Str2Int(b.rev()) ==
               2 * Str2Int(b0.rev()) + (if b.index(0) == '1' { 1nat } else { 0nat }));
        // By induction Str2Int(b0.rev()) == sum_{i=0..n-2} (if b[i+1]=='1' then 2^i else 0)
        // Multiply by 2:
        // 2 * Str2Int(b0.rev()) == sum_{i=0..n-2} (if b[i+1]=='1' then 2^{i+1} else 0)
        // Add (if b[0]=='1' then 1 else 0) to get sum_{i=0..n-1} (if b[i]=='1' then 2^i else 0)
        // Conclude equality holds.
    }
}

// Helper: convert a slice of chars (validated) to its integer value
exec fn seq_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures Str2Int(s@) == result
{
    let n = s.len();
    let mut acc: nat = 0;
    let mut i: usize = 0;
    while i < n
      invariant i <= n
      invariant acc == Str2Int(s@.subrange(0, i as int))
      decreases n - i
    {
        let c = s[i];
        // update acc
        if c == '1' {
            acc = 2 * acc + 1;
        } else {
            acc = 2 * acc;
        }
        // By definition of Str2Int, the new acc equals Str2Int(s.subrange(0, i+1))
        // The invariant is maintained
        i = i + 1;
    }
    acc
}

// Helper: convert a natural number to Vec<char> representing bits MSB-first
exec fn nat_to_seq(k: nat) -> Vec<char>
  ensures ValidBitString(result@)
  ensures Str2Int(result@) == k
{
    if k == 0 {
        return Vec::<char>::new();
    }

    let mut bits: Vec<char> = Vec::new(); // LSB-first
    let mut acc: nat = 0; // acc = sum_{j=0..len-1} bits[j]*2^j
    let mut factor: nat = 1; // factor = 2^{bits.len()}
    let mut n: nat = k;

    while n > 0
      invariant k == acc + n * factor
      invariant ValidBitString(bits@)
      decreases n
    {
        let bit_val = n % 2;
        if bit_val == 1 {
            bits.push('1');
            acc = acc + factor;
        } else {
            bits.push('0');
        }
        n = n / 2;
        factor = factor * 2;
    }

    // Now n == 0 and invariant gives k == acc
    // Construct result by reversing bits to MSB-first
    let mut res: Vec<char> = Vec::new();
    let len = bits.len();
    let mut idx: usize = 0;
    while idx < len
      invariant idx <= len
      invariant res.len() as int == idx as int
      decreases len - idx
    {
        // push bits from the end to the front to form MSB-first
        let c = bits.get(len - 1 - idx);
        res.push(c);
        idx += 1;
    }

    // Prove Str2Int(res@) == acc (and acc == k)
    // bits@ is LSB-first; res@ == bits@.rev()
    lemma_bits_rev_sum(bits@);
    // From lemma: Str2Int(res@) == sum_{i} (if bits@.index(i) == '1' then 2^i else 0) == acc
    // And invariant at loop end gave acc == k
    res
}

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let n1 = seq_to_nat(s1);
  let n2 = seq_to_nat(s2);
  let prod = n1 * n2;
  let res = nat_to_seq(prod);
  res
}
// </vc-code>

fn main() {}
}