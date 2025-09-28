use vstd::prelude::*;

verus! {

spec fn contains(v: i32, a: Seq<i32>, n: int) -> bool {
    exists|j: int| 0 <= j < n && a[j] == v
}

spec fn upper_bound(v: i32, a: Seq<i32>, n: int) -> bool {
    forall|j: int| 0 <= j < n ==> a[j] <= v
}

spec fn is_max(m: i32, a: Seq<i32>, n: int) -> bool {
    contains(m, a, n) && upper_bound(m, a, n)
}

// <vc-helpers>
spec fn contains(v: i32, a: Seq<i32>, n: int) -> bool {
    exists|j: int| 0 <= j < n && a[j] == v
}

spec fn upper_bound(v: i32, a: Seq<i32>, n: int) -> bool {
    forall|j: int| 0 <= j < n ==> a[j] <= v
}

spec fn is_max(m: i32, a: Seq<i32>, n: int) -> bool {
    contains(m, a, n) && upper_bound(m, a, n)
}
// </vc-helpers>

// <vc-spec>
fn max(a: &[i32], n: usize) -> (max: i32)
    requires 0 < n <= a.len(),
    ensures is_max(max, a@, n as int),
// </vc-spec>
// <vc-code>
{
    let mut current_max = a[0];
    proof {
        let a_seq = a@;
        assert(a_seq.len() >= 1 && n as int >= 1);
        assert(0 <= 0 < 1 as int && a_seq[0] == current_max);
        assert(contains(current_max, a_seq, 1));
        assert(forall|j: int| 0 <= j < 1 as int ==> a_seq[j] <= current_max);
        assert(upper_bound(current_max, a_seq, 1));
        assert(is_max(current_max, a_seq, 1));
    }
    let mut i: usize = 1;
    while i < n
        invariant
            i <= n,
            a@.len() >= n as int,
            is_max(current_max, a@, i as int),
    {
        if a[i] > current_max {
            current_max = a[i];
            proof {
                let a_seq = a@;
                // Prove that all previous are <= new current_max
                assert(forall|j: int| 0 <= j < i as int ==> a_seq[j] <= current_max);
                // And for upper_bound for i+1
                assert(forall|j: int| 0 <= j < (i+1) as int ==> #[trigger] a_seq[j] <= current_max);
                // Prove contains
                assert(i as int < (i+1) as int && a_seq[i as int] == current_max);
                assert(contains(current_max, a_seq, (i + 1) as int));
                assert(upper_bound(current_max, a_seq, (i + 1) as int));
                assert(is_max(current_max, a_seq, (i + 1) as int));
            }
        } else {
            // When not updating, is_max should hold automatically by invariant, but assert for clarity
            proof {
                // Since loop invariant ensures is_max holds for i
                assert(is_max(current_max, a@, i as int));
                // To corroborate maintain for i+1
                assert(a@.len() >= (i+1) as int);
                assert(forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] <= current_max);
                assert(a@[(i as int)] <= current_max);
                assert(contains(current_max, a@, i as int)); // from invariant
                assert(upper_bound(current_max, a@, i as int)); // from invariant
                // So for i+1, contains still holds since exists j < i
                assert(upper_bound(current_max, a@, (i+1) as int)); // since a[i] <= current_max
                assert(is_max(current_max, a@, (i+1) as int));
            }
        }
        i = i + 1;
    }
    current_max
}
// </vc-code>

fn main() {}

}