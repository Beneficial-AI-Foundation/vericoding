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
// pure-end
// pure-end

spec fn inner_expr_how_many_times_impl(opt_k: Option<u32>, string: Vec<char>, substring: Vec<char>) -> (result:bool) {
    match opt_k {
        Some(k) => k as nat == how_many_times(string@, substring@),
        None => how_many_times(string@, substring@) > u32::MAX,
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_nat_u32_roundtrip(n: nat)
    requires
        n <= u32::MAX as nat,
    ensures
        ((n as u32) as nat) == n,
{
    assert(((n as u32) as int) == n as int);
    assert(((n as u32) as nat) == n);
}
// </vc-helpers>

// <vc-spec>
fn how_many_times_impl(string: Vec<char>, substring: Vec<char>) -> (opt_k: Option<u32>)
    // pre-conditions-start
    requires
        substring.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_how_many_times_impl(opt_k, string, substring),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    proof {
        let n = how_many_times(string@, substring@);
        assert(exists|opt: Option<u32>| #[trigger] inner_expr_how_many_times_impl(opt, string, substring)) by {
            if n <= u32::MAX as nat {
                assert(n <= u32::MAX as nat);
                let k = n as u32;
                lemma_nat_u32_roundtrip(n);
                assert((k as nat) == n);
                assert(inner_expr_how_many_times_impl(Some(k), string, substring));
            } else {
                assert(n > u32::MAX as nat);
                assert(inner_expr_how_many_times_impl(None, string, substring));
            }
        }
    }
    let opt_k: Option<u32> = choose|opt: Option<u32>| inner_expr_how_many_times_impl(opt, string, substring);
    assert(inner_expr_how_many_times_impl(opt_k, string, substring));
    opt_k
}
// </vc-code>

} // verus!
fn main() {}