use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum(s.skip(1))
    }
}
// pure-end
// pure-end

spec fn sum_other_way(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] + sum_other_way(s.take(s.len() - 1))
    }
}
// pure-end

// <vc-helpers>
proof fn sum_take_map_succ(s: Seq<i32>, k: int)
    requires
        0 <= k && k + 1 <= s.len(),
    ensures
        sum(s.take(k + 1).map(|_idx, v: i32| v as int))
            == sum(s.take(k).map(|_idx, v: i32| v as int)) + (s@[k] as int),
    decreases
        k,
{
    if k == 0 {
        assert(s.take(0).map(|_i, v: i32| v as int).len() == 0);
        assert(sum(s.take(0).map(|_i, v: i32| v as int)) == 0);

        assert(s.take(1).map(|_i, v: i32| v as int).len() == 1);
        assert(s.take(1).map(|_i, v: i32| v as int)@[0] == s@[0] as int);
        assert(sum(s.take(1).map(|_i, v: i32| v as int)) == s@[0] as int);
    } else {
        sum_take_map_succ(s, k - 1);

        let left = s.take(k + 1).map(|_i, v: i32| v as int);
        let right = s.take(k).map(|_i, v: i32| v as int) + seq![s@[k] as int];

        // lengths equal
        assert(left.len() == right.len());

        // element-wise equality
        assert(forall|j: int|
            0 <= j && j < left.len() ==>
                left@[j] == right@[j]
        );

        assert(left == right);

        // sum of seq![x] is x
        assert(sum(seq![s@[k] as int]) == s@[k] as int);

        // sum of concatenation equals sum of parts
        assert(sum(right) == sum(s.take(k).map(|_i, v: i32| v as int)) + sum(seq![s@[k] as int]));
        assert(sum(right) == sum(s.take(k).map(|_i, v: i32| v as int)) + (s@[k] as int));
        assert(sum(left) == sum(right));
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: bool)
    // pre-conditions-start
    requires
        forall|i: int|
            0 <= i <= operations@.len() ==> sum(operations@.take(i).map(|_idx, j: i32| j as int))
                <= i32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <==> exists|i: int|
            0 <= i <= operations@.len() && sum(operations@.take(i).map(|_idx, j: i32| j as int))
                < 0,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = operations@.len();
    let mut i: int = 0;
    let mut acc: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant acc == sum(operations@.take(i).map(|_idx, j: i32| j as int));
        decreases n - i;
    {
        let next = acc + (operations@[i] as int);
        if next < 0 {
            return true;
        }
        proof {
            sum_take_map_succ(operations@, i);
            assert(acc == sum(operations@.take(i).map(|_idx, j: i32| j as int)));
            assert(sum(operations@.take(i + 1).map(|_idx, j: i32| j as int)) == acc + (operations@[i] as int));
        }
        acc = next;
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {}
}