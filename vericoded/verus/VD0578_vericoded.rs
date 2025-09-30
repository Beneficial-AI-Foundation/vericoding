use vstd::prelude::*;

verus! {

// Given an array of characters, it filters all the vowels. ['d','e','l','i','g','h','t']-> ['e','i']
spec fn vowels() -> Set<char> {
    set!['a', 'e', 'i', 'o', 'u']
}

spec fn filter_vowels(xs: Seq<char>) -> Seq<char>
    decreases xs.len()
{
    if xs.len() == 0 {
        seq![]
    } else if vowels().contains(xs[xs.len() - 1]) {
        filter_vowels(xs.subrange(0, xs.len() - 1)).add(seq![xs[xs.len() - 1]])
    } else {
        filter_vowels(xs.subrange(0, xs.len() - 1))
    }
}

// <vc-helpers>
// Lemma to show that filtering an empty sequence gives an empty sequence
proof fn filter_vowels_empty()
    ensures filter_vowels(Seq::<char>::empty()) == Seq::<char>::empty()
{
}

// Lemma showing the relationship between filtering a sequence and its prefix plus one element
proof fn filter_vowels_append_one(xs: Seq<char>, c: char)
    ensures 
        filter_vowels(xs.push(c)) == if vowels().contains(c) {
            filter_vowels(xs).push(c)
        } else {
            filter_vowels(xs)
        }
    decreases xs.len()
{
    // The spec definition works from the end, so we need to relate it
    let full = xs.push(c);
    assert(full.len() == xs.len() + 1);
    assert(full[full.len() - 1] == c);
    assert(full.subrange(0, full.len() - 1) =~= xs);
}

// Helper lemma for loop invariant
proof fn filter_vowels_subrange_extend(xs: Seq<char>, i: int)
    requires 0 <= i < xs.len()
    ensures 
        filter_vowels(xs.subrange(0, i + 1)) == if vowels().contains(xs[i]) {
            filter_vowels(xs.subrange(0, i)).push(xs[i])
        } else {
            filter_vowels(xs.subrange(0, i))
        }
{
    let sub = xs.subrange(0, i + 1);
    let sub_prev = xs.subrange(0, i);
    assert(sub =~= sub_prev.push(xs[i]));
    filter_vowels_append_one(sub_prev, xs[i]);
}
// </vc-helpers>

// <vc-spec>
fn filter_vowels_array(xs: &[char]) -> (ys: Vec<char>)
    ensures filter_vowels(xs@) == ys@
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            result@ == filter_vowels(xs@.subrange(0, i as int)),
        decreases xs.len() - i
    {
        let c = xs[i];
        
        if c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' {
            proof {
                filter_vowels_subrange_extend(xs@, i as int);
                assert(vowels().contains(c));
            }
            result.push(c);
        } else {
            proof {
                filter_vowels_subrange_extend(xs@, i as int);
                assert(!vowels().contains(c));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(xs@.subrange(0, xs.len() as int) =~= xs@);
    }
    
    result
}
// </vc-code>

fn main() {}

}