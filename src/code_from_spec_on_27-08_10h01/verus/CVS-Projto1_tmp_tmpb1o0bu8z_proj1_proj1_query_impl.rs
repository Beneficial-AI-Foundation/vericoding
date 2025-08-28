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
proof fn sum_property(a: Seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= k <= j <= a.len()
    ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
    decreases j - i
{
    if i == j {
        assert(i == k && k == j);
        assert(sum(a, i, j) == 0);
        assert(sum(a, i, k) == 0);
        assert(sum(a, k, j) == 0);
    } else if k == j {
        assert(sum(a, k, j) == 0);
    } else if k == i {
        assert(sum(a, i, k) == 0);
    } else {
        sum_property(a, i, j - 1, k);
        assert(sum(a, i, j - 1) == sum(a, i, k) + sum(a, k, j - 1));
        assert(sum(a, i, j) == a[j - 1] + sum(a, i, j - 1));
        assert(sum(a, k, j) == a[j - 1] + sum(a, k, j - 1));
        assert(sum(a, i, j) == a[j - 1] + sum(a, i, k) + sum(a, k, j - 1));
        assert(sum(a, i, j) == sum(a, i, k) + (a[j - 1] + sum(a, k, j - 1)));
        assert(sum(a, i, j) == sum(a, i, k) + sum(a, k, j));
    }
}

proof fn sum_single_element(a: Seq<int>, i: int)
    requires 0 <= i < a.len()
    ensures sum(a, i, i + 1) == a[i]
{
    assert(sum(a, i, i + 1) == a[(i + 1) - 1] + sum(a, i, (i + 1) - 1));
    assert(sum(a, i, i) == 0);
    assert(sum(a, i, i + 1) == a[i] + 0);
}

proof fn sum_map_preserves_value(a: Seq<i32>, i: int, j: int)
    requires 0 <= i <= j <= a.len()
    ensures sum(a.map(|k, x| x as int), i, j) == sum(a.map(|k, x| x as int), i, j)
    decreases j - i
{
    if i == j {
    } else {
        sum_map_preserves_value(a, i, j - 1);
        assert(a.map(|k, x| x as int)[j - 1] == a[j - 1] as int);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
exec fn query(a: &[i32], i: usize, j: usize) -> (s: i32)
    requires 0 <= i <= j <= a.len()
    ensures s == sum(a@.map(|k, x| x as int), i as int, j as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut s = 0i32;
    let mut k = i;
    
    while k < j
        invariant 
            i <= k <= j,
            k <= a.len(),
            s == sum(a@.map(|idx, x| x as int), i as int, k as int),
            i < usize::MAX,
            j < usize::MAX,
            k < usize::MAX,
            a.len() < usize::MAX,
            forall|idx: int| i <= idx < k ==> -2147483648 <= a@[idx] as int <= 2147483647,
            -2147483648 <= s as int <= 2147483647
        decreases j - k
    {
        s = s + a[k];
        
        proof {
            let mapped_seq = a@.map(|idx, x| x as int);
            sum_property(mapped_seq, i as int, (k + 1) as int, k as int);
            sum_single_element(mapped_seq, k as int);
            assert(sum(mapped_seq, i as int, (k + 1) as int) == sum(mapped_seq, i as int, k as int) + sum(mapped_seq, k as int, (k + 1) as int));
            assert(sum(mapped_seq, k as int, (k + 1) as int) == mapped_seq[k as int]);
            assert(mapped_seq[k as int] == a@[k as int] as int);
            assert(s as int == sum(mapped_seq, i as int, k as int) + mapped_seq[k as int]);
            assert(s as int == sum(mapped_seq, i as int, (k + 1) as int));
        }
        
        k = k + 1;
    }
    
    s
}
// </vc-code>

fn main() {}

}