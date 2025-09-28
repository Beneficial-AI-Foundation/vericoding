use vstd::prelude::*;

verus! {

spec fn sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

spec fn has_addends(q: Seq<int>, x: int) -> bool {
    exists|i: int, j: int| 0 <= i < j < q.len() && q[i] + q[j] == x
}

spec fn is_valid_index<T>(q: Seq<T>, i: nat) -> bool {
    0 <= i < q.len()
}

spec fn are_ordered_indices<T>(q: Seq<T>, i: nat, j: nat) -> bool {
    0 <= i < j < q.len()
}

spec fn are_addends_indices(q: Seq<int>, x: int, i: nat, j: nat) -> bool
    recommends is_valid_index(q, i) && is_valid_index(q, j)
{
    q[i as int] + q[j as int] == x
}

spec fn has_addends_in_indices_range(q: Seq<int>, x: int, i: nat, j: nat) -> bool
    recommends are_ordered_indices(q, i, j)
{
    has_addends(q.subrange(i as int, (j + 1) as int), x)
}

spec fn loop_inv(q: Seq<int>, x: int, i: nat, j: nat, sum: int) -> bool {
    are_ordered_indices(q, i, j) &&
    has_addends_in_indices_range(q, x, i, j) &&
    are_addends_indices(q, sum, i, j)
}

// <vc-helpers>
proof fn lemma_drop_left(q: Seq<int>, x: int, i: nat, j: nat)
    requires sorted(q)
    requires 0 <= i < j < q.len()
    requires has_addends_in_indices_range(q, x, i, j)
    requires q[i as int] + q[j as int] < x
    ensures has_addends_in_indices_range(q, x, i + 1, j)
{
    proof {
        let sub = q.subrange(i as int, (j + 1) as int);
        // obtain witnesses a,b for sub such that sub[a] + sub[b] == x
        let (a, b) = choose(|a: int, b: int| 0 <= a < b < sub.len() && sub[a] + sub[b] == x) by {
            assert(has_addends(sub, x));
        };
        let i_int = i as int;
        let j_int = j as int;
        let A_int = a + i_int;
        let B_int = b + i_int;
        assert(i_int <= A_int);
        assert(A_int < B_int);
        assert(B_int <= j_int);

        if a == 0 {
            // derive contradiction: sub[0] + sub[b] == x but sub[b] <= sub[j-i] and sub[0] + sub[j-i] == q[i] + q[j] < x
            // show sub[b] <= sub[j-i] using sorted(q)
            // sub[b] == q[i_int + b], sub[j-i] == q[j_int]
            assert(i_int + b <= j_int);
            // by sortedness of q
            assert(q[i_int + b] <= q[j_int]);
            // relate back to sub
            assert(sub[b] == q[i_int + b]);
            assert(sub[(j_int - i_int) as int] == q[j_int]);
            assert(sub[b] <= sub[(j_int - i_int) as int]);
            assert(sub[0] + sub[b] <= sub[0] + sub[(j_int - i_int) as int]);
            assert(sub[0] + sub[(j_int - i_int) as int] == q[i as int] + q[j as int]);
            assert(sub[0] + sub[b] < x);
            // but sub[0] + sub[b] == x, contradiction
            assert(false);
        } else {
            // a > 0, so we can shift both indices by -1 for the subrange starting at i+1
            let sub2 = q.subrange((i + 1) as int, (j + 1) as int);
            // show mapping: sub2[a-1] == sub[a] and sub2[b-1] == sub[b]
            assert(sub2[a - 1] == sub[a]);
            assert(sub2[b - 1] == sub[b]);
            assert(0 <= a - 1);
            assert(a - 1 < b - 1);
            assert(b - 1 < sub2.len());
            assert(sub2[a - 1] + sub2[b - 1] == x);
            assert(has_addends(sub2, x));
        }
    }
}

proof fn lemma_drop_right(q: Seq<int>, x: int, i: nat, j: nat)
    requires sorted(q)
    requires 0 <= i < j < q.len()
    requires has_addends_in_indices_range(q, x, i, j)
    requires q[i as int] + q[j as int] > x
    ensures has_addends_in_indices_range(q, x, i, j - 1)
{
    proof {
        let sub = q.subrange(i as int, (j + 1) as int);
        let (a, b) = choose(|a: int, b: int| 0 <= a < b < sub.len() && sub[a] + sub[b] == x) by {
            assert(has_addends(sub, x));
        };
        let i_int = i as int;
        let j_int = j as int;
        let A_int = a + i_int;
        let B_int = b + i_int;
        assert(i_int <= A_int);
        assert(A_int < B_int);
        assert(B_int <= j_int);

        if b == (j_int - i_int) {
            // derive contradiction: sub[a] + sub[last] == x but sub[a] >= sub[0] and sub[0] + sub[last] == q[i] + q[j] > x
            assert(sub[a] >= sub[0]);
            assert(sub[a] + sub[b] >= sub[0] + sub[b]);
            assert(sub[0] + sub[b] == q[i as int] + q[j as int]);
            assert(sub[a] + sub[b] > x);
            assert(false);
        } else {
            // b < j - i, so both a and b are valid indices in the shortened subrange
            let sub2 = q.subrange(i as int, j as int); // excludes original last element
            // show sub2[a] == sub[a] and sub2[b] == sub[b]
            assert(sub2[a] == sub[a]);
            assert(sub2[b] == sub[b]);
            assert(0 <= a);
            assert(a < b);
            assert(b < sub2.len());
            assert(sub2[a] + sub2[b] == x);
            assert(has_addends(sub2, x));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_addends(q: Seq<int>, x: int) -> (result: (usize, usize))
    requires sorted(q) && has_addends(q, x)
    ensures ({
        let (i, j) = result;
        i < j < q.len() && q[i as int] + q[j as int] == x
    })
// </vc-spec>
// <vc-code>
{
    let n: usize = q.len();
    let mut i: usize = 0;
    let mut j: usize = n - 1;

    // Establish that there are addends in the full range and that n >= 2 so 0 < n-1
    proof {
        let (a0, b0) = choose(|a: int, b: int| 0 <= a < b < q.len() && q[a] + q[b] == x) by {
            assert(has_addends(q, x));
        };
        // from 0 <= a0 < b0 and b0 < q.len() we get q.len() as int > 1, hence n >= 2
        assert((n as int) > 1);
        assert((i as int) < (j as int));
        assert(has_addends_in_indices_range(q, x, 0, n - 1));
    }

    while i < j && q[i as int] + q[j as int] != x
        invariant sorted(q)
        invariant i < j && j < n
        invariant has_addends_in_indices_range(q, x, i, j)
        decreases j - i
    {
        if q[i as int] + q[j as int] < x {
            proof {
                lemma_drop_left(q, x, i, j);
            }
            i += 1;
        } else {
            proof {
                lemma_drop_right(q, x, i, j);
            }
            j -= 1;
        }
    }

    (i, j)
}
// </vc-code>

fn main() {
}

}