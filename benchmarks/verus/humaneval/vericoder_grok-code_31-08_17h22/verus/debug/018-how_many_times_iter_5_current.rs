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
// </vc-helpers>
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
decreases(string.len())
{
    if string.is_empty() {
        Some(0)
    } else {
        let len_sub = substring.len() as usize;
        let is_prefix = {
            let len_str = string.len();
            if len_str < len_sub {
                false
            } else {
                let mut prefix = true;
                proof { }
                for i in 0..len_sub
                    invariant
                        prefix == (string@.subrange(0, i as int) == substring@.subrange(0, i as int)),
                        i <= len_sub,
                        len_str >= len_sub,
                {
                    if string[i] != substring[i] {
                        prefix = false;
                        proof {
                            assert(string@.subrange(0, i as int + 1) != substring@.subrange(0, i as int + 1));
                        }
                        break;
                    }
                }
                proof {
                    assert(prefix == (string@.subrange(0, len_sub as int) == substring@));
                }
                prefix
            }
        };
        let tail = vstd::vec![..string];
        tail.truncate(string.len() - 1);
        tail.remove(0);
        let recursive_result = how_many_times_impl(tail, substring);
        if is_prefix {
            match recursive_result {
                Some(c) if c < u32::MAX => Some(c + 1),
                _ => None,
            }
        } else {
            recursive_result
        }
    }
}
// </vc-code>
// </vc-code>

} // verus!
fn main() {}