use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

proof fn swap_preserves_multiset_helper(s: Seq<i32>, i: int, j: int)
    // pre-conditions-start
    requires
        0 <= i < j < s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        (s.take(j + 1)).to_multiset() =~= s.take(i).to_multiset().add(
            s.subrange(i + 1, j).to_multiset(),
        ).insert(s.index(j)).insert(s.index(i)),
    // post-conditions-end
{
    // impl-start
    let fst = s.take(i);
    let snd = s.subrange(i + 1, j);

    assert((s.take(j + 1)).to_multiset() =~= fst.to_multiset().insert(s.index(i)).add(
        snd.to_multiset().insert(s.index(j)),
    )) by {
        assert(s.take(i + 1).to_multiset() =~= fst.to_multiset().insert(s.index(i))) by {
            fst.to_multiset_ensures();
            assert(fst.push(s.index(i)) =~= s.take(i + 1));
        }
        assert(s.subrange(i + 1, j + 1).to_multiset() =~= snd.to_multiset().insert(s.index(j))) by {
            snd.to_multiset_ensures();
            assert(snd.push(s.index(j)) =~= s.subrange(i + 1, j + 1));
        }
        lemma_multiset_commutative(s.take(i + 1), s.subrange(i + 1, j + 1));
        assert(s.take(i + 1) + s.subrange(i + 1, j + 1) =~= s.take(j + 1));
    }
    // impl-end
}

proof fn swap_preserves_multiset(s1: Seq<i32>, s2: Seq<i32>, i: int, j: int)
    // pre-conditions-start
    requires
        0 <= i < j < s1.len() == s2.len(),
        forall|x: int| 0 <= x < s1.len() && x != i && x != j ==> s1.index(x) == s2.index(x),
        s1.index(i) == s2.index(j),
        s1.index(j) == s2.index(i),
    // pre-conditions-end
    // post-conditions-start
    ensures
        s1.to_multiset() == s2.to_multiset(),
    // post-conditions-end
{
    // impl-start
    calc! {
        (==)
        s1.to_multiset(); {
            lemma_multiset_commutative(s1.take(j + 1), s1.skip(j + 1));
            assert(s1 =~= s1.take(j + 1) + s1.skip(j + 1));
        }
        s1.take(j + 1).to_multiset().add(s1.skip(j + 1).to_multiset()); {
            assert(s1.take(j + 1).to_multiset() =~= s2.take(j + 1).to_multiset()) by {
                assert(s1.take(i) == s2.take(i));
                assert(s1.subrange(i + 1, j) =~= (s2.subrange(i + 1, j)));
                swap_preserves_multiset_helper(s1, i, j);
                swap_preserves_multiset_helper(s2, i, j);
            }
            assert(s1.skip(j + 1).to_multiset() =~= s2.skip(j + 1).to_multiset()) by {
                assert(s1.skip(j + 1) =~= s2.skip(j + 1));
            }
        }
        s2.take(j + 1).to_multiset().add(s2.skip(j + 1).to_multiset()); {
            lemma_multiset_commutative(s2.take(j + 1), s2.skip(j + 1));
            assert(s2 =~= s2.take(j + 1) + s2.skip(j + 1));
        }
        s2.to_multiset();
    }
    // impl-end
}

fn sort_seq(s: &Vec<i32>) -> (ret: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < ret@.len() ==> ret@.index(i) <= ret@.index(j),
        ret@.len() == s@.len(),
        s@.to_multiset() == ret@.to_multiset(),
    // post-conditions-end
{
    let mut result = s.clone();
    let mut i = 0;
    
    while i < result.len()
        invariant
            result@.len() == s@.len(),
            s@.to_multiset() == result@.to_multiset(),
            forall|x: int, y: int| 0 <= x < y < i ==> result@.index(x) <= result@.index(y),
    {
        let mut j = i + 1;
        while j < result.len()
            invariant
                i < result.len(),
                i + 1 <= j <= result.len(),
                result@.len() == s@.len(),
                s@.to_multiset() == result@.to_multiset(),
                forall|x: int, y: int| 0 <= x < y < i ==> result@.index(x) <= result@.index(y),
                forall|k: int| i + 1 <= k < j ==> result@.index(i as int) <= result@.index(k),
        {
            /* code modified by LLM (iteration 1): use usize indices directly and move proof block with old_result declaration */
            if result[j] < result[i] {
                proof {
                    let old_result = result@;
                    let temp = result[i];
                    result.set(i, result[j]);
                    result.set(j, temp);
                    swap_preserves_multiset(old_result, result@, i as int, j as int);
                }
            }
            j += 1;
        }
        i += 1;
    }
    
    result
}

fn unique_sorted(s: Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
    // post-conditions-end
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result@.index(x) < result@.index(y),
            forall|j: int| #![auto] 0 <= j < result.len() ==> s@.contains(result@.index(j)),
            forall|j: int| 0 <= j < i && s@.contains(s@.index(j)) ==> result@.contains(s@.index(j)),
    {
        if result.len() == 0 || result[result.len() - 1] != s[i] {
            result.push(s[i]);
        }
        i += 1;
    }
    
    result
}

fn unique(s: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
    // post-conditions-end
{
    let sorted = sort_seq(&s);
    unique_sorted(sorted)
}

}
fn main() {}