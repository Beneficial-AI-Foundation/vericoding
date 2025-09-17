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
/* helper modified by LLM (iteration 2): add loop invariants and decreases for termination */
fn first_one_index(v: &Vec<char>) -> usize {
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
        decreases v.len() - i
    {
        if v[i] == '1' {
            return i;
        }
        i += 1;
    }
    v.len()
}

/* helper modified by LLM (iteration 2): compare with proper loop invariants and decreases */
fn compare_ge(a: &Vec<char>, b: &Vec<char>) -> bool {
    let ia = first_one_index(a);
    let ib = first_one_index(b);
    let la = if ia == a.len() { 0 } else { a.len() - ia };
    let lb = if ib == b.len() { 0 } else { b.len() - ib };
    if la != lb {
        return la > lb;
    }
    let mut i: usize = 0;
    while i < la
        invariant
            i <= la,
        decreases la - i
    {
        let ca = a[ia + i];
        let cb = b[ib + i];
        if ca != cb {
            return ca == '1' && cb == '0';
        }
        i += 1;
    }
    true
}

/* helper modified by LLM (iteration 2): subtraction loop invariants and decreases for termination */
fn sub_vec(a: &Vec<char>, b: &Vec<char>) -> Vec<char> {
    let mut res_rev: Vec<char> = Vec::new();
    let mut borrow: i8 = 0;
    let mut k: usize = 0;
    while k < a.len()
        invariant
            k <= a.len(),
        decreases a.len() - k
    {
        let ai = a.len() - 1 - k;
        let abit = if a[ai] == '1' { 1 } else { 0 };
        let bbit = if k < b.len() {
            if b[b.len() - 1 - k] == '1' { 1 } else { 0 }
        } else { 0 };
        let mut diff = (abit as i8) - (bbit as i8) - borrow;
        if diff < 0 {
            diff += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        res_rev.push(if diff == 1 { '1' } else { '0' });
        k += 1;
    }
    let mut res: Vec<char> = Vec::new();
    let mut j = res_rev.len();
    while j > 0
        invariant
            j <= res_rev.len(),
        decreases j
    {
        j -= 1;
        res.push(res_rev[j]);
    }
    res
}

// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added loop invariants and decreases to ensure termination */
    let mut q: Vec<char> = Vec::new();
    let mut r: Vec<char> = Vec::new();

    let mut divisor_v: Vec<char> = Vec::new();
    let mut di: usize = 0;
    while di < divisor.len()
        invariant
            di <= divisor.len(),
        decreases divisor.len() - di
    {
        divisor_v.push(divisor[di]);
        di += 1;
    }

    let n = dividend.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
        decreases n - i
    {
        r.push(dividend[i]);
        if compare_ge(&r, &divisor_v) {
            r = sub_vec(&r, &divisor_v);
            q.push('1');
        } else {
            q.push('0');
        }
        i += 1;
    }

    (q, r)
}
// </vc-code>

fn main() {}
}

