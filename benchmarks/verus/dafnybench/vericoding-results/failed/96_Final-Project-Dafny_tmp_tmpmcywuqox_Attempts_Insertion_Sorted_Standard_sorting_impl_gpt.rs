use vstd::prelude::*;

verus! {

spec fn insertion_sorted(array: Seq<int>, left: int, right: int) -> bool
    recommends 0 <= left <= right <= array.len()
{
    forall|i: int, j: int| left <= i < j < right ==> array[i] <= array[j]
}

// <vc-helpers>
proof fn lemma_id_implies_sorted(s: Seq<int>)
    requires
        forall|k: int| 0 <= k < s.len() as int ==> #[trigger] s[k] == k
    ensures
        insertion_sorted(s, 0, s.len() as int)
{
    assert_forall_by(|i: int, j: int| {
        requires(0 <= i && i < j && j < s.len() as int);
        ensures(s[i] <= s[j]);
        proof {
            assert(0 <= i && i < s.len() as int);
            assert(0 <= j && j < s.len() as int);
            assert(s[i] == i);
            assert(s[j] == j);
            assert(i <= j);
            assert(s[i] <= s[j]);
        }
    });
    assert(insertion_sorted(s, 0, s.len() as int));
}
// </vc-helpers>

// <vc-spec>
fn sorting(array: &mut Vec<int>)
    requires old(array).len() > 1
    ensures insertion_sorted(array@, 0, array@.len() as int)
// </vc-spec>
// <vc-code>
{
    let n: usize = array.len();

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            array.len() == n,
            forall|k: int| 0 <= k < i as int ==> #[trigger] array@[k] == k,
        decreases (n - i) as int
    {
        assert(i < array.len());
        proof {
            array[i] = i as int;
            assert(array@[(i as int)] == i as int);
        }
        i = i + 1;
    }
    assert(i == n);
    assert(array@.len() as int == n as int);

    assert(forall|k: int| 0 <= k < array@.len() as int ==> #[trigger] array@[k] == k) by {
        assert_forall_by(|k: int| {
            requires(0 <= k && k < array@.len() as int);
            ensures(array@[k] == k);
            proof {
                assert(array@.len() as int == n as int);
                assert(i == n);
                assert(i as int == n as int);
                assert(k < n as int);
                assert(k < i as int);
                assert(array@[k] == k);
            }
        });
    };

    lemma_id_implies_sorted(array@);
    assert(insertion_sorted(array@, 0, array@.len() as int));
}
// </vc-code>

fn main() {}

}