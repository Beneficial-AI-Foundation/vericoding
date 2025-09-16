// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn how_many_times(string: Seq<char>, substring: Seq<char>) -> (result:nat)
    decreases string.len(),
{
    if (string.len() == 0) {
        0
    } else if substring.is_prefix_of(string) {
        1 + how_many_times(string.skip(1), substring)
    } else {
        how_many_times(string.skip(1), substring)
    }
}

spec fn inner_expr_how_many_times_impl(opt_k: Option<u32>, string: Vec<char>, substring: Vec<char>) -> (result:bool) {
    match opt_k {
        Some(k) => k as nat == how_many_times(string@, substring@),
        None => how_many_times(string@, substring@) > u32::MAX,
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): characterize prefix equivalence between Vec and Seq indices */
proof fn seq_prefix_chars_equiv(string: Vec<char>, substring: Vec<char>, i: int)
    requires
        i >= 0,
        (i as nat) + substring.len() <= string.len(),
    ensures
        (forall |j: int| j >= 0 && (j as nat) < substring.len() ==> string@[i + j] == substring@[j]) ==> substring@.is_prefix_of(string@.skip(i)),
        substring@.is_prefix_of(string@.skip(i)) ==> (forall |j: int| j >= 0 && (j as nat) < substring.len() ==> string@[i + j] == substring@[j]),
{
}

/* helper modified by LLM (iteration 5): how_many_times yields 0 when remaining string shorter than substring */
proof fn how_many_times_short_strings(s: Seq<char>, sub: Seq<char>)
    requires
        s.len() < sub.len(),
    ensures
        how_many_times(s, sub) == 0,
{
}

// </vc-helpers>

// <vc-spec>
fn how_many_times_impl(string: Vec<char>, substring: Vec<char>) -> (opt_k: Option<u32>)

    requires
        substring.len() >= 1,

    ensures
        inner_expr_how_many_times_impl(opt_k, string, substring),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implement scanning with int casts for spec calls and maintain spec invariant */
{
    let n = string.len();
    let m = substring.len();
    let mut i: usize = 0;
    let mut count: u64 = 0;
    while i + m <= n
        invariant
            i <= n,
            (count as nat) + how_many_times(string@.skip(i as int), substring@) == how_many_times(string@, substring@),
        decreases n - i
    {
        let mut j: usize = 0;
        let mut is_pref: bool = true;
        while j < m
            invariant
                j <= m,
                (is_pref ==> (forall |k: int| k >= 0 && k < (j as int) ==> string@[i as int + k] == substring@[k])),
            decreases m - j
        {
            if is_pref {
                if string[i + j] == substring[j] {
                    j = j + 1;
                } else {
                    is_pref = false;
                    j = j + 1;
                }
            } else {
                j = j + 1;
            }
        }
        if is_pref {
            proof {
                assert(substring@.is_prefix_of(string@.skip(i as int)));
            }
            count = count + 1;
        }
        i = i + 1;
    }
    proof {
        assert(i + m > n);
        assert((n - i) < m);
        assert(string@.skip(i as int).len() == (n - i) as nat);
        assert((n - i) as nat < substring@.len());
        how_many_times_short_strings(string@.skip(i as int), substring@);
        assert(how_many_times(string@.skip(i as int), substring@) == 0);
    }
    if count <= u64::from(u32::MAX) {
        Some(count as u32)
    } else {
        None
    }
}

// </vc-code>

}
fn main() {}