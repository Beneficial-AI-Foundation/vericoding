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
    if substring[0] == string.subrange(0, substring.len() as int)[0] && substring.skip(1) =~= string.skip(1).subrange(0, substring.skip(1).len() as int) {
        assert(substring[0] == string.subrange(0, substring.len() as int)[0]);
        assert(substring.skip(1) =~= string.skip(1).subrange(0, substring.skip(1).len() as int));
        
        let sub_len = substring.len() as int;
        let string_sub = string.subrange(0, sub_len);
        
        assert(substring.len() == string_sub.len());
        
        if substring.len() == 1 {
            assert(substring =~= seq![substring[0]]);
            assert(string_sub =~= seq![string_sub[0]]);
            assert(substring[0] == string_sub[0]);
        } else {
            assert(string.skip(1).subrange(0, substring.skip(1).len() as int) =~= string_sub.skip(1));
            assert(substring.skip(1) =~= string_sub.skip(1));
        }
    }
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
    if string.len() == 0 {
        // Base case: empty string
    } else {
        // Recursive case
        assert(!substring.is_prefix_of(string)); // substring is longer than string
        assert(string.skip(1).len() < substring.len());
        lemma_how_many_times_zero(string.skip(1), substring);
    }
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
    let mut i: usize = 0;
    
    while i < string.len()
        invariant
            0 <= i <= string.len(),
            substring.len() >= 1,
            count as nat == how_many_times(string@.subrange(0, i as int), substring@),
            count <= u32::MAX,
    {
        if i + substring.len() <= string.len() {
            let prefix_check = is_prefix(substring.clone(), string[i..i + substring.len()].to_vec());
            if prefix_check {
                if count == u32::MAX {
                    return None;
                }
                count += 1;
            }
        }
        i += 1;
    }
    
    Some(count)
}

} // verus!
fn main() {}