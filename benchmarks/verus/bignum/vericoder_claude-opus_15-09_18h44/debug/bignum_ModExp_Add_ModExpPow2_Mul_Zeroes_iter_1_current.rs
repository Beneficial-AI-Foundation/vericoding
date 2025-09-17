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

spec fn add_binary_spec(a: Seq<char>, b: Seq<char>) -> Seq<char>
    recommends
        ValidBitString(a),
        ValidBitString(b)
{
    if Str2Int(a) + Str2Int(b) == 0 {
        seq!['0']
    } else {
        int_to_binary_spec((Str2Int(a) + Str2Int(b)) as nat)
    }
}

spec fn int_to_binary_spec(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else if n % 2 == 0 {
        int_to_binary_spec(n / 2).push('0')
    } else {
        int_to_binary_spec(n / 2).push('1')
    }
}

proof fn lemma_int_to_binary_valid(n: nat)
    ensures
        ValidBitString(int_to_binary_spec(n))
    decreases n
{
    if n == 0 {
    } else {
        lemma_int_to_binary_valid(n / 2);
    }
}

proof fn lemma_int_to_binary_correct(n: nat)
    ensures
        n > 0 ==> Str2Int(int_to_binary_spec(n)) == n
    decreases n
{
    if n == 0 {
    } else if n % 2 == 0 {
        lemma_int_to_binary_correct(n / 2);
        if n / 2 > 0 {
            lemma_str2int_append_zero(int_to_binary_spec(n / 2));
        }
    } else {
        lemma_int_to_binary_correct(n / 2);
        if n / 2 > 0 {
            lemma_str2int_append_one(int_to_binary_spec(n / 2));
        } else {
            assert(int_to_binary_spec(n / 2) == seq![]);
            assert(int_to_binary_spec(n) == seq!['1']);
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let a_val = Str2Int(a@);
    let b_val = Str2Int(b@);
    let sum = a_val + b_val;
    
    if sum == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            assert(result@ == seq!['0']);
            assert(ValidBitString(result@));
        }
        return result;
    }
    
    let mut n = sum;
    let mut result = Vec::<char>::new();
    let mut temp = Vec::<char>::new();
    
    while n > 0
        invariant
            forall |i: int| 0 <= i && i < temp.len() ==> (temp@[i] == '0' || temp@[i] == '1'),
            n <= sum,
            ValidBitString(temp@)
    {
        if n % 2 == 0 {
            temp.push('0');
        } else {
            temp.push('1');
        }
        n = n / 2;
    }
    
    let len = temp.len();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall |j: int| 0 <= j && j < i ==> result@[j] == temp@[len - 1 - j],
            ValidBitString(result@),
            ValidBitString(temp@)
    {
        result.push(temp[len - 1 - i]);
        i = i + 1;
    }
    
    proof {
        lemma_int_to_binary_valid(sum);
        assert(ValidBitString(result@));
    }
    
    return result;
}
// </vc-code>

fn main() {}
}

