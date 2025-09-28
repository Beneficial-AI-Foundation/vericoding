// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_hex_char(c: char) -> bool {
    '0' <= c <= '9' || 'A' <= c <= 'F'
}

spec fn is_valid_hex_string(s: Seq<char>) -> bool {
    forall|i: int| #![auto] 0 <= i < s.len() ==> is_hex_char(s[i])
}

spec fn is_prime_hex_digit(c: char) -> bool {
    c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'
}

spec fn count_prime_hex_digits(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if is_prime_hex_digit(s[0]) { 1int } else { 0int }) + count_prime_hex_digits(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): helpers to bridge exec/spec and lemmas for sequence counting */
fn is_prime_hex_digit_exec(c: char) -> (b: bool) {
    c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'
}

proof fn is_prime_hex_digit_exec_spec_equiv(c: char)
    ensures
        is_prime_hex_digit(c) == is_prime_hex_digit_exec(c),
{
    assert(is_prime_hex_digit(c) == (c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'));
    assert(is_prime_hex_digit_exec(c) == (c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'));
}

proof fn count_concat_singleton(s1: Seq<char>, c: char)
    ensures
        count_prime_hex_digits(s1 + seq![c])
        == count_prime_hex_digits(s1) + (if is_prime_hex_digit(c) { 1int } else { 0int }),
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(count_prime_hex_digits(seq![c])
            == (if is_prime_hex_digit(seq![c][0]) { 1int } else { 0int }) + count_prime_hex_digits(seq![c].subrange(1, seq![c].len() as int)));
        assert(seq![c].subrange(1, seq![c].len() as int).len() == 0);
    } else {
        let h = s1[0];
        let t = s1.subrange(1, s1.len() as int);
        assert((s1 + seq![c]).len() == s1.len() + 1);
        assert((s1 + seq![c])[0] == h);
        assert((s1 + seq![c]).subrange(1, (s1 + seq![c]).len() as int) == t + seq![c]);
        count_concat_singleton(t, c);
        assert(count_prime_hex_digits(t + seq![c])
            == count_prime_hex_digits(t) + (if is_prime_hex_digit(c) { 1int } else { 0int }));
    }
}

/* helper modified by LLM (iteration 3): lemma about extending subrange with the next element */
proof fn subrange_extend_with_index_char(s: Seq<char>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        s.subrange(0, i + 1) == s.subrange(0, i) + seq![s[i]],
{
    let pre = s.subrange(0, i);
    let e = s[i];
    assert(pre.len() == i);
    assert((pre + seq![e]).len() == i + 1);

    assert forall |k:int| 0 <= k < i implies (pre + seq![e])[k] == s[k] by {
        assert((pre + seq![e])[k] == pre[k]);
        assert(pre[k] == s[k]);
    };
    assert((pre + seq![e])[i] == seq![e][0]);
    assert(seq![e][0] == e);
    assert(e == s[i]);

    assert(s.subrange(0, i + 1).len() == (pre + seq![e]).len());
    assert forall |k:int| 0 <= k < (pre + seq![e]).len() implies s.subrange(0, i + 1)[k] == (pre + seq![e])[k] by {
        if k < i {
            assert(s.subrange(0, i + 1)[k] == s[k]);
            assert((pre + seq![e])[k] == s[k]);
        } else {
            assert(k == i);
            assert(s.subrange(0, i + 1)[i] == s[i]);
            assert((pre + seq![e])[i] == s[i]);
        }
    };
}

/* helper modified by LLM (iteration 3): lemma that count is bounded by length */
proof fn count_leq_len(s: Seq<char>)
    ensures
        count_prime_hex_digits(s) <= s.len(),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let t = s.subrange(1, s.len() as int);
        count_leq_len(t);
        assert((if is_prime_hex_digit(s[0]) { 1int } else { 0int }) <= 1int);
    }
}

// </vc-helpers>

// <vc-spec>
fn hex_key(num: &str) -> (count: usize)
    requires
        is_valid_hex_string(num@),
    ensures
        count as int >= 0,
        count as int <= num@.len(),
        count as int == count_prime_hex_digits(num@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): avoid complex &mut chains by using an iterator variable and nth(i); maintain loop invariant over prefix */
    let mut i: usize = 0;
    let mut count: usize = 0;
    let mut done: bool = false;

    while !done
        invariant
            is_valid_hex_string(num@),
            0 <= i as int,
            i as int <= num@.len(),
            count as int == count_prime_hex_digits(num@.subrange(0, i as int)),
        decreases num@.len() - i as int
    {
        let mut it = num.chars();
        match it.nth(i) {
            Some(c) => {
                assert(c == num@[i as int]);
                proof { is_prime_hex_digit_exec_spec_equiv(c); }
                if is_prime_hex_digit_exec(c) {
                    count += 1;
                }
                proof {
                    subrange_extend_with_index_char(num@, i as int);
                    count_concat_singleton(num@.subrange(0, i as int), c);
                    assert(count_prime_hex_digits(num@.subrange(0, (i + 1) as int))
                        == count_prime_hex_digits(num@.subrange(0, i as int))
                           + (if is_prime_hex_digit(c) { 1int } else { 0int }));
                }
                i += 1;
            }
            None => {
                done = true;
            }
        }
    }

    proof {
        count_leq_len(num@);
        assert(count as int <= num@.len());
    }

    count
}
// </vc-code>


}

fn main() {}