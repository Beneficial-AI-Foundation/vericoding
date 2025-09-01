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
        how_many_times(string.skip((i + 1) as int), substring) == how_many_times(string.skip(i as int), substring) - if substring.is_prefix_of(string.skip(i as int)) { 1nat } else { 0nat },
    decreases string.len() - i,
{
    let s = string.skip(i as int);
    assert(s.len() == string.len() - i);
    assert(s.skip(1) =~= string.skip((i + 1) as int));
}

proof fn how_many_times_empty_substring_lemma(string: Seq<char>, substring: Seq<char>)
    requires
        substring.len() == 0,
    ensures
        how_many_times(string, substring) == 0,
    decreases string.len(),
{
    if string.len() == 0 {
        assert(how_many_times(string, substring) == 0);
    } else {
        assert(!substring.is_prefix_of(string));
        how_many_times_empty_substring_lemma(string.skip(1), substring);
    }
}

proof fn how_many_times_substring_too_long_lemma(string: Seq<char>, substring: Seq<char>)
    requires
        substring.len() > string.len(),
    ensures
        how_many_times(string, substring) == 0,
    decreases string.len(),
{
    if string.len() == 0 {
        assert(how_many_times(string, substring) == 0);
    } else {
        assert(!substring.is_prefix_of(string));
        assert(substring.len() > string.skip(1).len());
        how_many_times_substring_too_long_lemma(string.skip(1), substring);
    }
}

proof fn how_many_times_take_skip_relation(string: Seq<char>, substring: Seq<char>, i: nat)
    requires
        i <= string.len(),
    ensures
        how_many_times(string, substring) == how_many_times(string.take(i as int), substring) + how_many_times(string.skip(i as int), substring),
    decreases i,
{
    if i == 0 {
        assert(string.take(0) =~= Seq::<char>::empty());
        assert(string.skip(0) =~= string);
        assert(how_many_times(string.take(0), substring) == 0);
    } else {
        how_many_times_take_skip_relation(string, substring, (i - 1) as nat);
        assert(string.take(i as int) =~= string.take((i - 1) as int).push(string[(i - 1) as int]));
        let prev_take = string.take((i - 1) as int);
        let curr_take = string.take(i as int);
        assert(curr_take.skip((i - 1) as int) =~= Seq::<char>::new(1, |j: int| string[(i - 1) as int]));
        
        if substring.is_prefix_of(string.skip((i - 1) as int)) {
            assert(how_many_times(string.skip((i - 1) as int), substring) == 1 + how_many_times(string.skip(i as int), substring));
        } else {
            assert(how_many_times(string.skip((i - 1) as int), substring) == how_many_times(string.skip(i as int), substring));
        }
    }
}

fn is_prefix_at(string: &Vec<char>, substring: &Vec<char>, pos: usize) -> (result: bool)
    requires
        pos <= string.len(),
        substring.len() >= 1,
        pos as int + substring.len() as int <= usize::MAX,
    ensures
        result == substring@.is_prefix_of(string@.skip(pos as int)),
{
    if pos > string.len() - substring.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i < substring.len()
        invariant
            i <= substring.len(),
            pos + substring.len() <= string.len(),
            forall|j: nat| j < i ==> #[trigger] string@.skip(pos as int)[j as int] == substring@[j as int],
        decreases substring.len() - i,
    {
        if string[pos + i] != substring[i] {
            assert(string@.skip(pos as int)[i as int] != substring@[i as int]);
            return false;
        }
        i = i + 1;
    }
    
    assert forall|j: nat| j < substring@.len() implies #[trigger] string@.skip(pos as int)[j as int] == substring@[j as int] by {
        assert(substring@.len() == substring.len());
    }
    assert(substring@.is_prefix_of(string@.skip(pos as int)));
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
    if substring.len() == 0 {
        proof {
            how_many_times_empty_substring_lemma(string@, substring@);
        }
        return Some(0);
    }
    
    if substring.len() > string.len() {
        proof {
            how_many_times_substring_too_long_lemma(string@, substring@);
        }
        return Some(0);
    }
    
    let mut count: u32 = 0;
    let mut i: usize = 0;
    
    proof {
        assert(string@.take(0) =~= Seq::<char>::empty());
        assert(how_many_times(string@.take(0), substring@) == 0);
        how_many_times_take_skip_relation(string@, substring@, 0);
    }
    
    while i <= string.len()
        invariant
            i <= string.len(),
            substring.len() >= 1,
            count as nat == how_many_times(string@.take(i as int), substring@),
            how_many_times(string@, substring@) == how_many_times(string@.take(i as int), substring@) + how_many_times(string@.skip(i as int), substring@),
        decreases string.len() - i,
    {
        if i == string.len() {
            assert(string@.skip(i as int).len() == 0);
            assert(how_many_times(string@.skip(i as int), substring@) == 0);
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
            let old_i = i;
            how_many_times_skip_lemma(string@, substring@, i as nat);
            assert(string@.take((i + 1) as int) =~= string@.take(i as int).push(string@[i as int]));
            
            if is_match {
                assert(substring@.is_prefix_of(string@.skip(i as int)));
                assert(how_many_times(string@.skip(i as int), substring@) == 1 + how_many_times(string@.skip((i + 1) as int), substring@));
                assert(how_many_times(string@.take((i + 1) as int), substring@) == count as nat);
            } else {
                assert(!substring@.is_prefix_of(string@.skip(i as int)));
                assert(how_many_times(string@.skip(i as int), substring@) == how_many_times(string@.skip((i + 1) as int), substring@));
                assert(how_many_times(string@.take((i + 1) as int), substring@) == count as nat);
            }
            
            how_many_times_take_skip_relation(string@, substring@, (i + 1) as nat);
        }
        
        i = i + 1;
    }
    
    assert(count as nat == how_many_times(string@, substring@));
    Some(count)
}
// </vc-code>

} // verus!
fn main() {}