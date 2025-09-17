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
/* helper modified by LLM (iteration 2): added bit predicates and lemmas to maintain ValidBitString when building vectors */
spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }

/* helper modified by LLM (iteration 2): added bit predicates and lemmas to maintain ValidBitString when building vectors */
spec fn bit(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }

/* helper modified by LLM (iteration 2): prove singleton sequence is a valid bitstring */
proof fn lemma_valid_bitstring_singleton(c: char)
    requires
        is_bit(c),
    ensures
        ValidBitString(seq![c]),
{
    assert_forall_by(|i: int| {
        requires 0 <= i && i < (seq![c]).len() as int;
        ensures (seq![c]).index(i) == '0' || (seq![c]).index(i) == '1';
        {
            assert(i == 0);
            if c == '0' {
                assert(seq![c].index(i) == '0');
            } else {
                assert(c == '1');
                assert(seq![c].index(i) == '1');
            }
        }
    });
}

/* helper modified by LLM (iteration 2): prove pushing a bit preserves ValidBitString */
proof fn lemma_valid_bitstring_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        is_bit(c),
    ensures
        ValidBitString(s + seq![c]),
{
    assert_forall_by(|i: int| {
        requires 0 <= i && i < (s + seq![c]).len() as int;
        ensures (s + seq![c]).index(i) == '0' || (s + seq![c]).index(i) == '1';
        {
            let sl: int = s.len() as int;
            if i < sl {
                assert((s + seq![c]).index(i) == s.index(i));
                assert(s.index(i) == '0' || s.index(i) == '1');
            } else {
                assert((s + seq![c]).len() as int == sl + 1);
                assert(i == sl);
                assert((s + seq![c]).index(i) == seq![c].index(0));
                if c == '0' {
                    assert(seq![c].index(0) == '0');
                } else {
                    assert(c == '1');
                    assert(seq![c].index(0) == '1');
                }
            }
        }
    });
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): replaced isize indices with usize and added proof steps to maintain ValidBitString invariants during pushes and copies */
    let mut i1: usize = s1.len();
    let mut i2: usize = s2.len();
    let mut borrow: u8 = 0;
    let mut res_rev: Vec<char> = Vec::new();
    while i1 > 0 || i2 > 0
        invariant
            ValidBitString(res_rev@),
            i1 <= s1.len(),
            i2 <= s2.len(),
        decreases
            (i1 + i2) as nat
    {
        let c1 = if i1 > 0 { s1[i1 - 1] } else { '0' };
        let c2 = if i2 > 0 { s2[i2 - 1] } else { '0' };
        let b1: i32 = if c1 == '1' { 1 } else { 0 };
        let b2: i32 = if c2 == '1' { 1 } else { 0 };
        let mut val: i32 = b1 - b2 - (borrow as i32);
        if val < 0 {
            val += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        let ch = if val == 1 { '1' } else { '0' };
        proof {
            assert(is_bit(ch));
            lemma_valid_bitstring_push(res_rev@, ch);
        }
        res_rev.push(ch);
        if i1 > 0 { i1 -= 1; }
        if i2 > 0 { i2 -= 1; }
    }

    let mut res: Vec<char> = Vec::new();
    let mut j: usize = res_rev.len();
    while j > 0
        invariant
            ValidBitString(res@),
            j <= res_rev.len(),
        decreases
            j as nat
    {
        let ch2 = res_rev[j - 1];
        proof {
            let i: int = j as int - 1;
            assert(0 <= i && i < res_rev@.len() as int);
            assert(res_rev@.index(i) == '0' || res_rev@.index(i) == '1');
            assert(is_bit(ch2));
            lemma_valid_bitstring_push(res@, ch2);
        }
        res.push(ch2);
        j -= 1;
    }

    // Trim leading zeros while keeping at least one digit
    let mut k: usize = 0;
    while k < res.len() && res[k] == '0'
        invariant
            k <= res.len(),
        decreases
            (res.len() - k) as nat
    {
        k += 1;
    }
    if k == res.len() {
        let mut zero_vec: Vec<char> = Vec::new();
        proof { lemma_valid_bitstring_singleton('0'); }
        zero_vec.push('0');
        return zero_vec;
    }
    if k > 0 {
        let mut trimmed: Vec<char> = Vec::new();
        let mut t: usize = k;
        while t < res.len()
            invariant
                ValidBitString(trimmed@),
                t <= res.len(),
            decreases
                (res.len() - t) as nat
        {
            let ch3 = res[t];
            proof {
                let i: int = t as int;
                assert(0 <= i && i < res@.len() as int);
                assert(res@.index(i) == '0' || res@.index(i) == '1');
                assert(is_bit(ch3));
                lemma_valid_bitstring_push(trimmed@, ch3);
            }
            trimmed.push(ch3);
            t += 1;
        }
        return trimmed;
    }
    res
}
// </vc-code>

fn main() {}
}


