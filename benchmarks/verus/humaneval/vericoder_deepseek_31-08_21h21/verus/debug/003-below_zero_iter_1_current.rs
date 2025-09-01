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
proof fn lemma_sum_take_eq_len<A>(s: Seq<A>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        s.take(n).len() == n,
{
}

proof fn lemma_take_map_len<A, B>(v: Vec<A>, f: FnSpec(A) -> B, n: int)
    requires
        0 <= n <= v@.len(),
    ensures
        v@.take(n).map(f).len() == n,
{
    lemma_sum_take_eq_len(v@, n);
}

proof fn lemma_seq_map_index<A, B>(s: Seq<A>, f: FnSpec(A) -> B, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.map(f)@[i] == f(s[i]),
{
}

proof fn lemma_take_map_index<A, B>(v: Vec<A>, f: FnSpec(A) -> B, n: int, i: int)
    requires
        0 <= n <= v@.len(),
        0 <= i < n,
    ensures
        v@.take(n).map(f)@[i] == f(v@[i]),
{
    lemma_seq_map_index(v@.take(n), f, i);
}

proof fn lemma_sum_recursive(s: Seq<int>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        sum(s.take(i)) == if i == 0 { 0 } else { sum(s.take(i - 1)) + s[i - 1] },
    decreases i,
{
    if i > 0 {
        lemma_sum_recursive(s, i - 1);
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
    let mut total = 0;
    let mut i: usize = 0;
    while i < operations.len()
        invariant
            0 <= i <= operations@.len(),
            total == sum(operations@.take(i).map(|_idx, j: i32| j as int)),
            forall|k: int| i <= k <= operations@.len() ==> 
                sum(operations@.take(k).map(|_idx, j: i32| j as int)) >= 0,
        decreases operations@.len() - i,
    {
        let op = operations.index(i);
        total = total + op as int;
        proof {
            lemma_take_map_len(operations, |j: i32| j as int, i + 1);
            lemma_take_map_index(operations, |j: i32| j as int, i + 1, i);
            lemma_sum_recursive(operations@.map(|_idx, j: i32| j as int), i + 1);
        }
        if total < 0 {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {}
}