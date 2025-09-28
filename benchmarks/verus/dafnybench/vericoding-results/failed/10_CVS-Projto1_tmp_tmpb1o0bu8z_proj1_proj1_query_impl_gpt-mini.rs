use vstd::prelude::*;

verus! {

//Exercicio 1.a)
spec fn sum(a: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
    decreases j when 0 <= i <= j <= a.len()
{
    if i == j {
        0
    } else {
        a[j - 1] + sum(a, i, j - 1)
    }
}

//Exercicio 1.b)

//Exercicio 1.c)


spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool {
    a.len() + 1 == c.len()
    && c[0] == 0
    && forall|j: int| 1 <= j <= a.len() ==> c[j] == sum(a, 0, j)
}

///Exercicio 2.
#[derive(PartialEq, Eq)]
enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> }
}

fn from_array<T: Copy>(a: &[T]) -> (l: List<T>)
    requires a.len() > 0
    ensures forall|j: int| 0 <= j < a.len() ==> mem(a@[j], l)
{
    assume(false);
    List::Nil
}

spec fn mem<T>(x: T, l: List<T>) -> bool
    decreases l
{
    match l {
        List::Nil => false,
        List::Cons { head: y, tail: r } => if x == y { true } else { mem(x, *r) }
    }
}

// <vc-helpers>
proof fn sum_zero(a: Seq<int>, i: int)
    requires 0 <= i <= a.len()
    ensures sum(a, i, i) == 0
{
    // By definition of sum, when i == j it is 0.
    assert(sum(a, i, i) == 0);
}

proof fn sum_succ(a: Seq<int>, i: int, k: int)
    requires 0 <= i <= k < a.len()
    ensures sum(a, i, k + 1) == a@[k] + sum(a, i, k)
{
    // By definition of sum, for i <= k < a.len(), sum(a,i,k+1) = a[k] + sum(a,i,k)
    assert(sum(a, i, k + 1) == a@[k] + sum(a, i, k));
}
// </vc-helpers>

// <vc-spec>
exec fn query(a: &[i32], i: usize, j: usize) -> (s: i32)
    requires 0 <= i <= j <= a.len()
    ensures s == sum(a@.map(|k, x| x as int), i as int, j as int)
// </vc-spec>
// <vc-code>
{
    let seqA = a@.map(|_, x| x as int);
    let mut k: usize = i;
    let mut acc: int = 0;
    // Establish initial invariant facts
    proof {
        // k == i holds by initialization
        assert(k == i);
        // acc == sum(seqA, i, k) because acc == 0 and sum(..., i, i) == 0
        sum_zero(seqA, i as int);
        assert(acc == sum(seqA, i as int, k as int));
    }
    while k < j
        invariant (i <= k && k <= j)
        invariant acc == #[trigger] sum(seqA, i as int, k as int)
        decreases (j as int) - (k as int)
    {
        let old_k = k;
        let old_acc = acc;
        let v: int = a[old_k] as int;
        acc = old_acc + v;
        k = old_k + 1;
        proof {
            // From the loop invariant before the step
            assert(old_acc == sum(seqA, i as int, old_k as int));
            // Use the lemma for sum at successor to unfold the sum
            sum_succ(seqA, i as int, old_k as int);
            assert(sum(seqA, i as int, (old_k as int) + 1) == seqA@[(old_k as int)] + sum(seqA, i as int, old_k as int));
            // Relate seqA indexing to array a
            assert(seqA@[(old_k as int)] == a[old_k] as int);
            // Combine to get the new invariant
            assert(acc == sum(seqA, i as int, k as int));
        }
    }
    acc as i32
}
// </vc-code>

fn main() {}

}