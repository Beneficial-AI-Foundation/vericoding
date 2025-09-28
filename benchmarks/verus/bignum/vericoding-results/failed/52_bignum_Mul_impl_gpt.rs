// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 {
    0nat 
  } else {
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 7): rewrite forall proof using `assert forall|...| ... by {}` to avoid closure syntax issues */
proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires
        valid_bit_string(s),
        c == '0' || c == '1'
    ensures
        valid_bit_string(s.push(c))
{
    assert(s.push(c).len() == s.len() + 1);
    assert forall|i: int|
        0 <= i < s.push(c).len() ==> (s.push(c)[i] == '0' || s.push(c)[i] == '1')
    by {
        if i < s.len() {
            assert(0 <= i < s.len());
            assert(s.push(c)[i] == s[i]);
            assert(valid_bit_string(s));
            assert(s[i] == '0' || s[i] == '1');
        } else {
            assert(!(i < s.len()));
            assert(i == s.len());
            assert(s.push(c)[i] == c);
            assert(c == '0' || c == '1');
        }
    };
    assert(forall|i: int| 0 <= i < s.push(c).len() ==> (s.push(c)[i] == '0' || s.push(c)[i] == '1'));
}

/* helper modified by LLM (iteration 7): spec constructor from nat to bitstring sequence */
spec fn nat_to_seq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0nat {
        Seq::empty()
    } else {
        let rest = nat_to_seq(n / 2nat);
        let c: char = if n % 2nat == 1nat { '1' } else { '0' };
        rest.push(c)
    }
}

/* helper modified by LLM (iteration 7): str2int over push */
proof fn lemma_str2int_push(s: Seq<char>, c: char)
    ensures
        str2int(s.push(c)) == 2nat * str2int(s) + (if c == '1' { 1nat } else { 0nat })
{
    assert(s.push(c).len() == s.len() + 1);
    assert(
        str2int(s.push(c))
        == 2nat * str2int(s.push(c).subrange(0, s.push(c).len() - 1))
           + (if s.push(c)[s.push(c).len() - 1] == '1' { 1nat } else { 0nat })
    );
    assert(s.push(c).subrange(0, s.push(c).len() - 1) == s);
    assert(s.push(c)[s.push(c).len() - 1] == c);
}

/* helper modified by LLM (iteration 7): properties of nat_to_seq (validity and correctness) */
proof fn lemma_nat_to_seq_properties(n: nat)
    ensures
        valid_bit_string(nat_to_seq(n)),
        str2int(nat_to_seq(n)) == n
    decreases n
{
    if n == 0nat {
        assert(valid_bit_string(nat_to_seq(n)));
        assert(str2int(nat_to_seq(n)) == n);
    } else {
        lemma_nat_to_seq_properties(n / 2nat);
        let s_prev = nat_to_seq(n / 2nat);
        let c: char = if n % 2nat == 1nat { '1' } else { '0' };
        lemma_valid_bit_string_push(s_prev, c);
        lemma_str2int_push(s_prev, c);
        assert(str2int(s_prev) == n / 2nat);
        proof {
            if n % 2nat == 1nat {
                assert(c == '1');
            } else {
                assert(n % 2nat == 0nat);
                assert(c == '0');
            }
        }
        assert((if c == '1' { 1nat } else { 0nat }) == n % 2nat);
        assert(2nat * (n / 2nat) + (n % 2nat) == n);
        assert(nat_to_seq(n) == s_prev.push(c));
        assert(valid_bit_string(nat_to_seq(n)));
        assert(str2int(nat_to_seq(n)) == 2nat * (n / 2nat) + (n % 2nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): build result by converting product nat to bitstring vector */
    let ghost prod: nat = str2int(s1@) * str2int(s2@);
    proof { lemma_nat_to_seq_properties(prod); }
    let res: Vec<char> = Vec::from_seq(nat_to_seq(prod));
    proof {
        assert(res@ == nat_to_seq(prod));
        assert(valid_bit_string(res@));
        assert(str2int(res@) == prod);
    }
    res
}
// </vc-code>


}

fn main() {}