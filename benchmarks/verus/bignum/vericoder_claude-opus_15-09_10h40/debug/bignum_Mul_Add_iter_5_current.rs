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
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    let s_new = s.push('0');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    let s_new = s.push('1');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == '1');
}

spec fn add_bit_strings(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    recommends
        ValidBitString(s1),
        ValidBitString(s2)
{
    if Str2Int(s1) + Str2Int(s2) == 0 {
        seq!['0']
    } else {
        int_to_bit_string((Str2Int(s1) + Str2Int(s2)) as nat)
    }
}

spec fn int_to_bit_string(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else if n % 2 == 0 {
        int_to_bit_string(n / 2).push('0')
    } else {
        int_to_bit_string(n / 2).push('1')
    }
}

proof fn lemma_int_to_bit_string_valid(n: nat)
    ensures
        ValidBitString(int_to_bit_string(n))
    decreases n
{
    if n > 0 {
        lemma_int_to_bit_string_valid(n / 2);
    }
}

proof fn lemma_int_to_bit_string_correct(n: nat)
    ensures
        n == 0 ==> int_to_bit_string(n).len() == 0,
        n > 0 ==> Str2Int(int_to_bit_string(n)) == n
    decreases n
{
    if n > 0 {
        lemma_int_to_bit_string_correct(n / 2);
        lemma_int_to_bit_string_valid(n / 2);
        if n % 2 == 0 {
            lemma_str2int_append_zero(int_to_bit_string(n / 2));
        } else {
            lemma_str2int_append_one(int_to_bit_string(n / 2));
        }
    }
}

/* helper modified by LLM (iteration 5): Added decreases clause to inner loop */
exec fn multiply_bit_strings(s1: &[char], s2: &[char]) -> (result: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@)
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@)
{
    if s1.len() == 0 || s2.len() == 0 || (s1.len() == 1 && s1[0] == '0') || (s2.len() == 1 && s2[0] == '0') {
        return vec!['0'];
    }
    
    let mut result = vec!['0'];
    let mut multiplier = Vec::<char>::new();
    let mut j: usize = 0;
    while j < s1.len()
        invariant
            j <= s1.len(),
            multiplier@.len() == j,
            multiplier@ == s1@.subrange(0, j as int)
        decreases s1.len() - j
    {
        multiplier.push(s1[j]);
        j = j + 1;
    }
    
    let mut i: usize = s2.len();
    
    while i > 0
        invariant
            i <= s2.len(),
            ValidBitString(result@),
            ValidBitString(multiplier@),
            multiplier@ == s1@
        decreases i
    {
        i = i - 1;
        if s2[i] == '1' {
            result = add_exec(result, multiplier.clone());
        }
        if i > 0 {
            multiplier.push('0');
            proof {
                lemma_str2int_append_zero(multiplier@.subrange(0, multiplier@.len() as int - 1));
            }
        }
    }
    
    result
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

exec fn add_exec(s1: Vec<char>, s2: Vec<char>) -> (result: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@)
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@)
{
    let n1 = str_to_int_exec(&s1);
    let n2 = str_to_int_exec(&s2);
    let sum = n1 + n2;
    int_to_str_exec(sum)
}

exec fn str_to_int_exec(s: &[char]) -> (n: u64)
    requires
        ValidBitString(s@),
        Str2Int(s@) < 0x10000000000000000
    ensures
        n == Str2Int(s@)
{
    let mut n: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            n == Str2Int(s@.subrange(0, i as int))
        decreases s.len() - i
    {
        n = n * 2;
        if s[i] == '1' {
            n = n + 1;
        }
        i = i + 1;
    }
    n
}

exec fn int_to_str_exec(mut n: u64) -> (result: Vec<char>)
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n
{
    if n == 0 {
        return vec!['0'];
    }
    
    let orig_n = n;
    let mut result = Vec::<char>::new();
    let mut temp = Vec::<char>::new();
    while n > 0
        invariant
            ValidBitString(temp@)
        decreases n
    {
        if n % 2 == 0 {
            temp.push('0');
        } else {
            temp.push('1');
        }
        n = n / 2;
    }
    
    let mut i: usize = temp.len();
    while i > 0
        invariant
            i <= temp.len(),
            ValidBitString(result@)
        decreases i
    {
        i = i - 1;
        result.push(temp[i]);
    }
    
    proof {
        lemma_int_to_bit_string_valid(orig_n as nat);
        lemma_int_to_bit_string_correct(orig_n as nat);
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
    /* code modified by LLM (iteration 5): Calling multiply_bit_strings helper */
    multiply_bit_strings(s1, s2)
}
// </vc-code>

fn main() {}
}
