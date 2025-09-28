// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 3 && s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z'
}

spec fn valid_abbreviation(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() >= 3 &&
    s.len() >= 3 &&
    result[0] == s[0] &&
    result[result.len() - 1] == s[s.len() - 1] &&
    result == seq![s[0]].add(int_to_string(s.len() - 2)).add(seq![s[s.len() - 1]])
}

spec fn int_to_string(n: int) -> Seq<char>
    decreases if n >= 0 { n } else { -n }
{
    if n == 0 {
        seq!['0']
    } else if n < 0 {
        seq!['-'].add(int_to_string_helper(-n))
    } else {
        int_to_string_helper(n)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    recommends n >= 0
    decreases n
{
    if n <= 0 {
        Seq::new(0 as nat, |_i: int| ' ')
    } else {
        int_to_string_helper(n / 10).add(seq![(('0' as int) + (n % 10)) as char])
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): push digits according to spec int_to_string_helper */
fn push_digits(v: &mut Vec<char>, n: usize)
    ensures
        v@ == old(v)@.add(int_to_string_helper(n as int)),
    decreases n
{
    if n == 0 {
        // int_to_string_helper(0) is empty; nothing to append
    } else {
        push_digits(v, n / 10);
        let d: char = (('0' as u8) + ((n % 10) as u8)) as char;
        v.push(d);
    }
}

/* helper modified by LLM (iteration 3): relate int_to_string to helper for positive integers */
proof fn int_pos_equals_helper(n: int)
    requires
        n > 0,
    ensures
        int_to_string(n) == int_to_string_helper(n),
{
    assert(int_to_string(n) == int_to_string_helper(n));
}

/* helper modified by LLM (iteration 3): int_to_string_helper(n) has length >= 1 for n > 0 */
proof fn lemma_int_to_string_helper_pos_len(n: int)
    requires
        n > 0,
    ensures
        int_to_string_helper(n).len() >= 1,
    decreases n
{
    // For n > 0, the definition appends one digit
    assert(int_to_string_helper(n) == int_to_string_helper(n / 10).add(seq![((('0' as int) + (n % 10)) as char)]));
    assert(int_to_string_helper(n).len() == int_to_string_helper(n / 10).len() + 1);
    assert(int_to_string_helper(n).len() >= 1);
}

/* helper modified by LLM (iteration 3): int_to_string(n) has length >= 1 for n > 0 */
proof fn lemma_int_to_string_pos_len(n: int)
    requires
        n > 0,
    ensures
        int_to_string(n).len() >= 1,
{
    int_pos_equals_helper(n);
    lemma_int_to_string_helper_pos_len(n);
    assert(int_to_string(n).len() == int_to_string_helper(n).len());
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_abbreviation(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): construct abbreviation and prove spec equality and properties */
    proof { assert(s.len() >= 3); }

    let n: usize = s.len() - 2;

    let mut r: Vec<char> = Vec::new();
    let snap0 = r@;
    r.push(s[0]);
    let snap1 = r@;
    push_digits(&mut r, n);
    let snap2 = r@;
    let last_idx: usize = s.len() - 1;
    r.push(s[last_idx]);
    let snap3 = r@;

    proof {
        // Basic arithmetic facts
        let n_int: int = s.len() as int - 2;
        assert(n_int == n as int);
        assert(n_int > 0);

        // Unfold effects of pushes/appends
        assert(snap1 == snap0.push(s[0]));
        assert(snap0 == Seq::empty());
        assert(Seq::empty().push(s[0]) == seq![s[0]]);
        assert(snap1 == seq![s[0]]);

        assert(snap2 == snap1.add(int_to_string_helper(n as int)));
        assert(snap3 == snap2.push(s[last_idx]));
        assert(snap3 == seq![s[0]].add(int_to_string_helper(n_int)).push(s[last_idx]));
        assert(seq![s[0]].add(int_to_string_helper(n_int)).push(s[last_idx])
               == seq![s[0]].add(int_to_string_helper(n_int)).add(seq![s[last_idx]]));

        // Connect helper and full int_to_string for positive n
        int_pos_equals_helper(n_int);
        assert(seq![s[0]].add(int_to_string_helper(n_int)) == seq![s[0]].add(int_to_string(n_int)));

        assert(r@ == seq![s[0]].add(int_to_string(n_int)).add(seq![s[last_idx]]));

        // Length and endpoints
        lemma_int_to_string_pos_len(n_int);
        assert(r@.len() >= 3);
        assert(r@[0] == s[0]);
        assert(r@[r.len() - 1] == s[last_idx]);

        assert(valid_abbreviation(s@, r@));
    }

    r
}
// </vc-code>


}

fn main() {}