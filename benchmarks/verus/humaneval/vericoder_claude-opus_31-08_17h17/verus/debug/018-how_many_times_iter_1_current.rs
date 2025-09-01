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
proof fn how_many_times_skip_lemma(string: Seq<char>, substring: Seq<char>, i: nat)
    requires
        i < string.len(),
    ensures
        how_many_times(string.skip(i + 1), substring) == how_many_times(string.skip(i), substring) - if substring.is_prefix_of(string.skip(i)) { 1 } else { 0 },
    decreases string.len() - i,
{
    let s = string.skip(i);
    assert(s.len() == string.len() - i);
    assert(s.skip(1) =~= string.skip(i + 1));
}

fn is_prefix_at(string: &Vec<char>, substring: &Vec<char>, pos: usize) -> (result: bool)
    requires
        pos <= string.len(),
        substring.len() >= 1,
    ensures
        result == substring@.is_prefix_of(string@.skip(pos as nat)),
{
    if pos + substring.len() > string.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i < substring.len()
        invariant
            i <= substring.len(),
            pos + substring.len() <= string.len(),
            forall|j: nat| j < i ==> #[trigger] string@.skip(pos as nat)[j] == substring@[j],
    {
        if string[pos + i] != substring[i] {
            assert(string@.skip(pos as nat)[i as nat] != substring@[i as nat]);
            return false;
        }
        i = i + 1;
    }
    
    assert forall|j: nat| j < substring@.len() implies #[trigger] string@.skip(pos as nat)[j] == substring@[j] by {
        assert(substring@.len() == substring.len());
    }
    assert(substring@.is_prefix_of(string@.skip(pos as nat)));
    true
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
    if substring.len() == 0 || substring.len() > string.len() {
        return Some(0);
    }
    
    let mut count: u32 = 0;
    let mut i: usize = 0;
    
    while i <= string.len()
        invariant
            i <= string.len(),
            substring.len() >= 1,
            count as nat == how_many_times(string@.take(i as nat), substring@),
            how_many_times(string@, substring@) == count as nat + how_many_times(string@.skip(i as nat), substring@),
    {
        if i == string.len() {
            assert(string@.skip(i as nat).len() == 0);
            assert(how_many_times(string@.skip(i as nat), substring@) == 0);
            break;
        }
        
        let is_match = is_prefix_at(&string, &substring, i);
        
        if is_match {
            if count == u32::MAX {
                assert(how_many_times(string@, substring@) > u32::MAX);
                return None;
            }
            count = count + 1;
        }
        
        proof {
            how_many_times_skip_lemma(string@, substring@, i as nat);
            assert(string@.take(i as nat + 1) =~= string@.take(i as nat).push(string@[i as nat]));
        }
        
        i = i + 1;
    }
    
    Some(count)
}
// </vc-code>

} // verus!
fn main() {}