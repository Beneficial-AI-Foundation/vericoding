use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

// <vc-helpers>
fn sorted_pred(s: Seq<int>, u: int, w: int) -> bool {
    0 <= u < w < s.len() ==> s[u] <= s[w]
}

proof fn lemma_sorted_transitive(s: Seq<int>, a: int, b: int, c: int)
    requires
        sorted(s),
        0 <= a < b < c < s.len(),
    ensures
        s[a] <= s[c],
{
    // Need to prove s[a] <= s[b] and s[b] <= s[c]
    // These are direct consequences of sorted(s)
    assert(s[a] <= s[b]) by {
        assert(sorted_pred(s, a, b));
    }
    assert(s[b] <= s[c]) by {
        assert(sorted_pred(s, b, c));
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search(v: &Vec<i32>, elem: i32) -> (p: i32)
    requires sorted(v@.map_values(|val: i32| val as int)),
    ensures ({
        &&& -1 <= p < v.len()
        &&& forall|u: int| 0 <= u <= p ==> v@[u] <= elem as int
        &&& forall|w: int| p < w < v.len() ==> v@[w] > elem as int
    }),
// </vc-spec>
// <vc-code>
{
    let mut low: usize = 0;
    let mut high: usize = v.len(); // Exclusive upper bound

    if v.len() == 0 {
        return -1;
    }

    while low < high
        invariant
            0 <= low as int <= high as int <= v.len() as int,
            forall|i: int| 0 <= i < low as int ==> v@[i] <= elem as int,
            forall|i: int| high as int <= i < v.len() as int ==> v@[i] > elem as int,
            sorted(v@.map_values(|val: i32| val as int)),
    {
        let mid: usize = low + (high - low) / 2;
        assert(low <= mid < high); // mid is always a valid index within the current range

        let s_elem: i32 = elem;
        let v_mid: i32 = v@[mid]; 

        if (v_mid <= s_elem) {
            low = mid + 1;
        } else {
            high = mid;
        }
    }

    // Post-loop: low == high
    // The invariant implies:
    // forall|i: int| 0 <= i < low ==> v@[i] <= elem as int
    // forall|i: int| low <= i < v.len() ==> v@[i] > elem as int (since high is now low)

    // We need to return an index p such that:
    // forall|u: int| 0 <= u <= p ==> v@[u] <= elem as int
    // forall|w: int| p < w < v.len() ==> v@[w] > elem as int

    // If low == 0, it means all elements are > elem or the array is empty.
    // If low > 0 and v@[low-1] <= elem, then p = low - 1 is the correct answer.
    // If v@[low-1] > elem, then it means all elements in the array are > elem,
    // and the first element satisfies this. In this case, p = -1.

    // Let's analyze the properties of 'low' at termination:
    // If low == 0:
    //   - The invariant `forall|i: int| 0 <= i < low ==> v@[i] <= elem as int` vacuously holds.
    //   - The invariant `forall|i: int| low <= i < v.len() ==> v@[i] > elem as int` becomes
    //     `forall|i: int| 0 <= i < v.len() ==> v@[i] > elem as int`.
    //   In this case, the correct `p` is -1.

    // If low > 0:
    //   - From `forall|i: int| 0 <= i < low ==> v@[i] <= elem as int`, we have `v@[low-1] <= elem`.
    //   - From `forall|i: int| low <= i < v.len() ==> v@[i] > elem as int`, we have `v@[low] > elem` (if low < v.len()).
    //   So, `p = low - 1` satisfies `v@[p] <= elem` and `v@[p+1] > elem`.
    //   This means all elements up to `p` are `<= elem`, and all after `p` are `> elem`.

    let p: i32 = low as i32 - 1;

    // Prove the first part of the ensures: 0 <= u <= p ==> v@[u] <= elem as int
    assert forall |u: int| 0 <= u <= p implies v@[u] <= elem as int by {
        if 0 <= u <= p {
            assert(u < low as int); // Since p = low - 1
            assert(v@[u] <= elem as int); // From loop invariant for `low`
        }
    } no_unwind;

    // Prove the second part of the ensures: p < w < v.len() ==> v@[w] > elem as int
    assert forall |w: int| p < w < v.len() implies v@[w] > elem as int by {
        if p < w < v.len() {
            assert(low as int - 1 < w);
            assert(low as int <= w); // Since low - 1 < w means w >= low
            assert(w < v.len() as int);
            assert(v@[w] > elem as int); // From loop invariant for `high` (which is now `low`)
        }
    } no_unwind;

    // Prove -1 <= p < v.len()
    // -1 <= p:
    // Since low >= 0, p = low - 1 >= -1.
    assert(p >= -1);

    // p < v.len():
    // low <= v.len() => low - 1 < v.len() => p < v.len().
    proof {
        assert(low as int <= v.len() as int);
        assert(p < v.len() as int);
    }

    p
}
// </vc-code>

//Recursive binary search

fn main() {}

}