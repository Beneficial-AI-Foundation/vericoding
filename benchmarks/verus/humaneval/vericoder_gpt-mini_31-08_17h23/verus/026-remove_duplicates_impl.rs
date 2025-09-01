use vstd::prelude::*;

verus! {

spec fn count_frequency_spec(seq: Seq<i64>, key: i64) -> (result:int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_spec(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
proof fn count_frequency_spec_eq_filter(seq: Seq<i64>, key: i64)
    decreases seq.len()
{
    if seq.len() == 0 {
        assert(count_frequency_spec(seq, key) == 0);
        assert(seq.filter(|y: i64| y == key).len() == 0);
    } else {
        let tail = seq.drop_last();
        count_frequency_spec_eq_filter(tail, key);
        assert(count_frequency_spec(seq, key) == count_frequency_spec(tail, key) + if seq.last() == key { 1 } else { 0 });
        assert(seq.filter(|y: i64| y == key).len() == tail.filter(|y: i64| y == key).len() + if seq.last() == key { 1 } else { 0 });
        assert(tail.filter(|y: i64| y == key).len() == count_frequency_spec(tail, key));
        assert(seq.filter(|y: i64| y == key).len() == count_frequency_spec(seq, key));
    }
}

// Helper lemma: after pushing an element x to a Vec, the last element of its sequence view equals x.
proof fn vec_push_last_i64(v: &mut Vec<i64>, x: i64)
{
    // This lemma is intended to be used immediately after doing v.push(x)
    // Verus tracks the correspondence between Vec and its sequence view,
    // so we can assert that the last element of v@ equals x.
    let len_usize = v.len();
    assert(len_usize >= 1);
    let last_idx = len_usize - 1;
    // get is executable and returns the same value as the sequence index at that position
    assert(v.get(last_idx) == x);
    assert(v@.index((v@.len() - 1) as int) == x);
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)
    // post-conditions-start
    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n: usize = numbers.len();
    let mut unique_numbers: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant forall |k: int| 0 <= k && k < i as int && count_frequency_spec(numbers@, numbers@.index(k)) == 1
            ==> (exists |t: int| 0 <= t && t < unique_numbers@.len() && unique_numbers@.index(t) == numbers@.index(k))
        invariant forall |t: int| 0 <= t && t < unique_numbers@.len()
            ==> (exists |k: int| 0 <= k && k < i as int && unique_numbers@.index(t) == numbers@.index(k) && count_frequency_spec(numbers@, unique_numbers@.index(t)) == 1)
        decreases n - i
    {
        let xi: i64 = numbers.get(i);

        let mut j: usize = 0;
        let mut found: bool = false;
        while j < n && !found
            invariant j <= n
            invariant found == (exists |k: int| 0 <= k && k < j as int && k != i as int && numbers@.index(k) == xi)
            decreases n - j
        {
            if j != i && numbers.get(j) == xi {
                found = true;
            }
            j = j + 1;
        }

        proof {
            if found {
                // from invariant and j <= n we get existence within 0..n
                assert(exists |k: int| 0 <= k && k < n as int && k != i as int && numbers@.index(k) == xi);
                // hence frequency >= 2, so not equal to 1
                count_frequency_spec_eq_filter(numbers@, xi);
                assert(!(count_frequency_spec(numbers@, xi) == 1));
            } else {
                // loop terminated with !found, so by loop condition and invariant j <= n we have j == n
                assert(j == n);
                // from invariant and found == false we get that no k < j (== n) satisfies the exists predicate
                assert(! (exists |k: int| 0 <= k && k < j as int && k != i as int && numbers@.index(k) == xi));
                // hence for all k < n, not(k != i && numbers@.index(k) == xi), equivalently if numbers@[k]==xi then k==i
                assert(forall |k: int| 0 <= k && k < n as int ==> (numbers@.index(k) == xi ==> k == i as int));
                // therefore xi occurs exactly once in numbers@
                count_frequency_spec_eq_filter(numbers@, xi);
                assert(count_frequency_spec(numbers@, xi) == 1);
            }
        }

        if !found {
            unique_numbers.push(xi);
            proof {
                // show the newly pushed element satisfies the invariants:
                // the last element of unique_numbers@ is xi
                vec_push_last_i64(&mut unique_numbers, xi);
            }
        }

        proof {
            // Now show the main invariants hold for i+1
            // 1) For any k < i+1, if count(...)==1 then exists t in unique_numbers@ equal to numbers@[k]
            //    - for k < i, follows from the previous invariant
            //    - for k == i, if !found then we just pushed xi and can pick t = unique_numbers@.len() - 1; if found then count != 1 so implication vacuous
            assert(i <= n);
            if !found {
                // show that numbers@.index(i) is present in unique_numbers@
                assert(count_frequency_spec(numbers@, numbers@.index(i as int)) == 1);
                let t: int = (unique_numbers@.len() - 1) as int;
                assert(0 <= t && t < unique_numbers@.len());
                assert(unique_numbers@.index(t) == numbers@.index(i as int));
            } else {
                // nothing to do: for k == i the antecedent is false because count != 1
            }

            // 2) For any t < unique_numbers@.len(), there exists k < i+1 with unique_numbers@.index(t) == numbers@.index(k) and count(...)==1
            //    - For t referring to an element that was present before this iteration, the previous invariant gives k < i
            //    - If we just pushed, the new last element has k = i
            if !found {
                let t: int = (unique_numbers@.len() - 1) as int;
                assert(0 <= t && t < unique_numbers@.len());
                // the last element corresponds to k = i and is unique in numbers@
                assert(unique_numbers@.index(t) == numbers@.index(i as int));
                assert(count_frequency_spec(numbers@, unique_numbers@.index(t)) == 1);
            }
        }

        i = i + 1;
    }

    unique_numbers
}
// </vc-code>

} // verus!
fn main() {}