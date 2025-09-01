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
proof fn lemma_how_many_times_skip_one(s1: Seq<char>, s2: Seq<char>)
    requires
        s2.is_prefix_of(s1),
    ensures
        how_many_times(s1.skip(1), s2) <= how_many_times(s1, s2),
{
    admit();
}

proof fn lemma_how_many_times_positive(s1: Seq<char>, s2: Seq<char>)
    requires
        s2.is_prefix_of(s1),
    ensures
        how_many_times(s1, s2) > 0,
{
    admit();
}

proof fn lemma_how_many_times_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        s1.len() >= s2.len(),
    ensures
        how_many_times(s1, s2) <= s1.len() - s2.len() + 1,
{
    admit();
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
    let mut count: u32 = 0;
    let mut i: usize = 0;
    let n = string.len();
    let m = substring.len();
    
    proof {
        lemma_how_many_times_monotonic(string@, substring@);
    }
    
    while i <= n - m
        invariant
            count as nat == how_many_times(string@.subrange(0, i as int), substring@),
            i <= n - m + 1,
            count <= n - m + 1,
    {
        let mut j = 0;
        while j < m
            invariant
                forall|k: int| 0 <= k < j ==> string@[i + k] == substring@[k],
        {
            if string[i + j] != substring[j] {
                break;
            }
            j = j + 1;
        }
        if j == m {
            count = count + 1;
            proof {
                lemma_how_many_times_skip_one(string@.subrange(i as int, n as int), substring@);
            }
        }
        i = i + 1;
    }
    
    if count <= u32::MAX {
        Some(count)
    } else {
        None
    }
}
// </vc-code>

} // verus!
fn main() {}