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
proof fn how_many_times_decreases(s: Seq<char>, sub: Seq<char>)
    ensures
        s.len() > 0 ==> s.skip(1).len() < s.len(),
{
    if s.len() > 0 {
        assert(s.skip(1).len() == s.len() - 1);
    }
}

proof fn prefix_property(s: Seq<char>, sub: Seq<char>)
    ensures
        sub.is_prefix_of(s) ==> s.len() > 0,
{
    if sub.is_prefix_of(s) {
        assert(sub.len() <= s.len());
        if s.len() == 0 {
            assert(sub.len() == 0);
        }
    }
}

proof fn skip_length_lemma(s: Seq<char>)
    ensures
        s.skip(1).len() == if s.len() > 0 { s.len() - 1 } else { 0 },
{
    if s.len() > 0 {
        assert(s.skip(1).len() == s.len() - 1);
    } else {
        assert(s.skip(1).len() == 0);
    }
}

fn find_next_occurrence(s: &Vec<char>, sub: &Vec<char>, start: usize) -> (idx: Option<usize>)
    requires
        sub@.len() >= 1,
        start <= s@.len(),
    ensures
        match idx {
            Some(i) => i >= start && i <= s@.len() - sub@.len() && sub@.is_prefix_of(s@.subrange(i as int, s@.len() as int)),
            None => forall|i: int| start as int <= i && i <= (s@.len() - sub@.len()) as int ==> !sub@.is_prefix_of(s@.subrange(i, s@.len() as int)),
        },
    decreases (s@.len() - start) as int,
{
    let mut idx = start;
    
    proof {
        if s@.len() < sub@.len() {
            assert(idx > s@.len() - sub@.len());
            return None;
        }
        assert(s@.len() >= sub@.len());
    }
    
    while idx <= s@.len() - sub@.len()
        invariant
            idx >= start,
            idx <= s@.len() - sub@.len() + 1,
            forall|i: int| start as int <= i && i < idx as int ==> !sub@.is_prefix_of(s@.subrange(i, s@.len() as int)),
        decreases (s@.len() - sub@.len() - idx) as int,
    {
        let mut match_found = true;
        let mut j = 0usize;
        
        while j < sub.len()
            invariant
                j <= sub@.len(),
                match_found ==> forall|k: int| 0 <= k && k < j as int ==> s@[idx as int + k] == sub@[k],
                !match_found ==> s@[idx as int] != sub@[0],
            decreases (sub@.len() - j) as int,
        {
            if j == 0 {
                assert(s@.len() > idx);
            }
            if s[idx + j] != sub[j] {
                match_found = false;
                break;
            }
            j += 1;
        }
        
        if match_found {
            return Some(idx);
        }
        idx += 1;
    }
    None
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
        return None;
    }

    let mut count: u32 = 0;
    let mut current_index: usize = 0;
    
    proof {
        assert(substring@.len() >= 1);
    }
    
    while current_index <= string.len() - substring.len()
        invariant
            current_index <= string@.len(),
            count as nat == how_many_times(string@, substring@) - how_many_times(string@.subrange(current_index as int, string@.len() as int), substring@),
        decreases (string@.len() - current_index) as int,
    {
        let occurrence = find_next_occurrence(&string, &substring, current_index);
        proof {
            how_many_times_decreases(string@.subrange(current_index as int, string@.len() as int), substring@);
        }
        match occurrence {
            Some(idx) => {
                proof {
                    prefix_property(string@.subrange(idx as int, string@.len() as int), substring@);
                    skip_length_lemma(string@.subrange(current_index as int, string@.len() as int));
                }
                count += 1;
                current_index = idx + 1;
                if count == u32::MAX {
                    return None;
                }
            },
            None => {
                break;
            }
        }
    }
    
    Some(count)
}
// </vc-code>

} // verus!
fn main() {}