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
// pure-end

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
// pure-end

fn sort_seq(s: &Vec<i32>) -> (ret: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < ret@.len() ==> ret@.index(i) <= ret@.index(j),
        ret@.len() == s@.len(),
        s@.to_multiset() == ret@.to_multiset(),
    // post-conditions-end
{
    let mut ret = s.clone();
    let mut i = 0;
    
    while i < ret.len()
        invariant
            ret@.len() == s@.len(),
            s@.to_multiset() == ret@.to_multiset(),
            forall|x: int, y: int| 0 <= x < y < i ==> ret@.index(x) <= ret@.index(y),
            forall|x: int, y: int| 0 <= x < i <= y < ret@.len() ==> ret@.index(x) <= ret@.index(y),
    {
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < ret.len()
            invariant
                i <= min_idx < ret.len(),
                i < j <= ret.len(),
                ret@.len() == s@.len(),
                s@.to_multiset() == ret@.to_multiset(),
                forall|k: int| i <= k < j ==> ret@.index(min_idx as int) <= ret@.index(k),
                forall|x: int, y: int| 0 <= x < y < i ==> ret@.index(x) <= ret@.index(y),
                forall|x: int, y: int| 0 <= x < i <= y < ret@.len() ==> ret@.index(x) <= ret@.index(y),
        {
            if ret[j] < ret[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            proof {
                swap_preserves_multiset(ret@, ret@.update(i as int, ret@.index(min_idx as int)).update(min_idx as int, ret@.index(i as int)), i as int, min_idx as int);
            }
            /* code modified by LLM (iteration 1): read values before swap to avoid borrowing conflicts */
            let temp = ret[i];
            let min_val = ret[min_idx];
            ret.set(i, min_val);
            ret.set(min_idx, temp);
        }
        i = i + 1;
    }
    
    ret
}

fn strange_sort_list_helper(s: &Vec<i32>) -> (ret: (Vec<i32>, Vec<i32>))
    // post-conditions-start
    ensures
        s@.to_multiset() == (ret.0)@.to_multiset(),
        s@.len() == (ret.0)@.len() == (ret.1)@.len(),
        forall|i: int|
            0 <= i < s@.len() && i % 2 == 0 ==> (ret.1)@.index(i) == (ret.0)@.index(i / 2),
        forall|i: int|
            0 <= i < s@.len() && i % 2 == 1 ==> (ret.1)@.index(i) == (ret.0)@.index(
                s@.len() - (i - 1) / 2 - 1,
            ),
    // post-conditions-end
{
    let sorted = sort_seq(s);
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < sorted.len()
        invariant
            sorted@.len() == s@.len(),
            s@.to_multiset() == sorted@.to_multiset(),
            result@.len() == i,
            forall|j: int|
                0 <= j < i && j % 2 == 0 ==> result@.index(j) == sorted@.index(j / 2),
            forall|j: int|
                0 <= j < i && j % 2 == 1 ==> result@.index(j) == sorted@.index(
                    s@.len() - (j - 1) / 2 - 1,
                ),
    {
        if i % 2 == 0 {
            result.push(sorted[i / 2]);
        } else {
            result.push(sorted[sorted.len() - (i - 1) / 2 - 1]);
        }
        i = i + 1;
    }
    
    (sorted, result)
}

fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)
    // post-conditions-start
    ensures
        s@.len() == ret@.len(),
    // post-conditions-end
{
    let (_, result) = strange_sort_list_helper(s);
    result
}

}
fn main() {}