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

proof fn lemma_step_subrange(substring: Seq<char>, string: Seq<char>)
    // pre-conditions-start
    requires
        substring.len() > 0,
        string.len() >= substring.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        (substring[0] == string.subrange(0, substring.len() as int)[0] && (substring.skip(1)
            =~= string.skip(1).subrange(0, substring.skip(1).len() as int))) ==> (substring
            =~= string.subrange(0, substring.len() as int)),
    decreases substring.len(),
    // post-conditions-end
{
    // impl-start
    if (substring[0] == string.subrange(0, substring.len() as int)[0] && (substring.skip(1)
        =~= string.skip(1).subrange(0, substring.skip(1).len() as int))) {
        assert forall|i: int| 0 <= i < substring.len() implies #[trigger] substring[i]
            == string.subrange(0, substring.len() as int)[i] by {
            if i == 0 {
            } else {
                assert(forall|j: int|
                    (0 <= #[trigger] (j + 0) < substring.len() - 1) ==> substring.skip(1)[j]
                        == string.skip(1).subrange(0, substring.skip(1).len() as int)[j]);
                assert(0 <= #[trigger] (i - 1 + 0) < substring.len() - 1);
            }
        }
    } else {
    }
    // impl-end
}
// pure-end

fn is_prefix(substring: Vec<char>, string: Vec<char>) -> (b: bool)
    // post-conditions-start
    ensures
        b == substring@.is_prefix_of(string@),
    // post-conditions-end
{
    if substring.len() > string.len() {
        return false;
    }
    
    let mut i = 0;
    while i < substring.len()
        invariant
            0 <= i <= substring.len(),
            substring.len() <= string.len(),
            /* code modified by LLM (iteration 1): fixed syntax error by replacing 'implies' with '==>' */
            forall|j: int| 0 <= j < i ==> substring@[j] == string@[j],
    {
        if substring[i] != string[i] {
            return false;
        }
        i += 1;
    }
    true
}

proof fn lemma_how_many_times_zero(string: Seq<char>, substring: Seq<char>)
    // pre-conditions-start
    requires
        string.len() < substring.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        how_many_times(string, substring) == 0,
    decreases string.len(),
    // post-conditions-end
{
    // impl-start
    if string.len() == 0 {
    } else {
        lemma_how_many_times_zero(string.skip(1), substring)
    }
    // impl-end
}
// pure-end

spec fn inner_expr_how_many_times_impl(opt_k: Option<u32>, string: Vec<char>, substring: Vec<char>) -> (result:bool) {
    match opt_k {
        Some(k) => k as nat == how_many_times(string@, substring@),
        None => how_many_times(string@, substring@) > u32::MAX,
    }
}
// pure-end

fn how_many_times_impl(string: Vec<char>, substring: Vec<char>) -> (opt_k: Option<u32>)
    // pre-conditions-start
    requires
        substring.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_how_many_times_impl(opt_k, string, substring),
    // post-conditions-end
{
    let mut count: u32 = 0;
    let mut i = 0;
    
    while i < string.len()
        invariant
            0 <= i <= string.len(),
            substring.len() >= 1,
            count as nat == how_many_times(string@.subrange(0, i as int), substring@),
    {
        if is_prefix(substring.clone(), Vec::from_iter(string.iter().skip(i).cloned())) {
            if count == u32::MAX {
                return None;
            }
            count += 1;
        }
        i += 1;
        
        proof {
            assert(string@.subrange(0, i as int) =~= string@.subrange(0, (i-1) as int).push(string@[i-1]));
            assert(string@.subrange(0, (i-1) as int).push(string@[i-1]).skip(1) =~= string@.subrange(1, i as int));
        }
    }
    
    proof {
        assert(string@.subrange(0, string.len() as int) =~= string@);
    }
    
    Some(count)
}

} // verus!
fn main() {}