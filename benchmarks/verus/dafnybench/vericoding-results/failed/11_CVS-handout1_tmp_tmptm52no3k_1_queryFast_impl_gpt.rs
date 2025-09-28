use vstd::prelude::*;

verus! {

/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

spec fn sum(a: Seq<int>, i: int, j: int) -> int
    decreases j - i
{
    if i >= j { 
        0 
    } else { 
        a[i] + sum(a, i + 1, j) 
    }
}



//(b)




//(c)

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool
{
    &&& a.len() + 1 == c.len() 
    &&& c.len() > 0 
    &&& c[0] == 0
    &&& forall|i: int| 0 <= i < a.len() ==> c[i + 1] == c[i] + a[i]
}

// <vc-helpers>
proof fn lemma_sum_snoc(a: Seq<int>, i: int, k: int)
    requires
        0 <= i <= k < a.len()
    ensures
        sum(a, i, k + 1) == sum(a, i, k) + a[k]
    decreases k - i + 1
{
    if i == k {
        assert(sum(a, i, i) == 0);
        assert(i < i + 1);
        assert(sum(a, i + 1, i + 1) == 0);
        assert(sum(a, i, i + 1) == a[i] + sum(a, i + 1, i + 1));
        assert(sum(a, i, i + 1) == a[i]);
    } else {
        assert(i < k);
        lemma_sum_snoc(a, i + 1, k);
        assert(sum(a, i, k) == a[i] + sum(a, i + 1, k));
        assert(sum(a, i, k + 1) == a[i] + sum(a, i + 1, k + 1));
        assert(sum(a, i + 1, k + 1) == sum(a, i + 1, k) + a[k]);
        assert(sum(a, i, k + 1) == (a[i] + sum(a, i + 1, k)) + a[k]);
        assert(sum(a, i, k + 1) == sum(a, i, k) + a[k]);
    }
}

proof fn lemma_prefix_sum_diff(a: Seq<int>, c: Seq<int>, i: int, j: int)
    requires
        is_prefix_sum_for(a, c),
        0 <= i <= j <= a.len()
    ensures
        c[j] - c[i] == sum(a, i, j)
    decreases j - i
{
    if i == j {
        assert(c[j] - c[i] == 0);
        assert(sum(a, i, j) == 0);
    } else {
        assert(i < j);
        assert(j > 0);
        let k = j - 1;
        assert(i <= k);
        assert(0 <= k && k < a.len());
        assert(c[k + 1] == c[k] + a[k]) by {
            assert(is_prefix_sum_for(a, c));
            assert(0 <= k && k < a.len());
        }
        lemma_prefix_sum_diff(a, c, i, k);
        assert(c[j] - c[i] == (c[k] - c[i]) + a[k]);
        lemma_sum_snoc(a, i, k);
        assert(sum(a, i, j) == sum(a, i, k) + a[k]);
    }
}
// </vc-helpers>

// <vc-spec>
fn queryFast(a: &[i32], c: &[i32], i: i32, j: i32) -> (r: i32)
    requires a.len() + 1 == c.len() && c.len() > 0 && c@[0] == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a@.map(|_i, x| x as int), c@.map(|_i, x| x as int))
    ensures r as int == sum(a@.map(|_i, x| x as int), i as int, j as int)
// </vc-spec>
// <vc-code>
{
    proof {
        assert((j as int) <= (a@).len());
        assert((i as int) <= (a@).len());
        assert((c@).len() == (a@).len() + 1);
        assert(0 <= j && 0 <= i);
        assert((j as int) < (c@).len());
        assert((i as int) < (c@).len());

        lemma_prefix_sum_diff(
            (a@).map(|_, x| x as int),
            (c@).map(|_, x| x as int),
            i as int,
            j as int,
        );
    }

    let r = c[j as int] - c[i as int];

    proof {
        assert(((c@).map(|_, x| x as int))[j as int] == (c@[j as int]) as int);
        assert(((c@).map(|_, x| x as int))[i as int] == (c@[i as int]) as int);
        assert(c@[j as int] == c[j as int]);
        assert(c@[i as int] == c[i as int]);

        assert(r as int == (c[j as int] as int) - (c[i as int] as int));
        assert(
            (c[j as int] as int) - (c[i as int] as int)
            == ((c@).map(|_, x| x as int))[j as int]
                - ((c@).map(|_, x| x as int))[i as int]
        );
        assert(
            ((c@).map(|_, x| x as int))[j as int]
                - ((c@).map(|_, x| x as int))[i as int]
            == sum((a@).map(|_, x| x as int), i as int, j as int)
        );
    }

    r
}
// </vc-code>

fn main() {}

}