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
proof fn sum_extend(a: Seq<int>, i: int, j: int)
    requires 0 <= i <= j < a.len()
    ensures sum(a, i, j + 1) == sum(a, i, j) + a[j]
    decreases a.len() - j
{
    reveal(sum);
    if j == i {
        assert(sum(a, i, i + 1) == a[i] + sum(a, i, i));
        assert(sum(a, i, i) == 0);
    } else {
        assert(sum(a, i, j + 1) == a[j] + sum(a, i, j));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn query(a: &[i32], i: usize, j: usize) -> (s: i32)
    requires 0 <= i <= j <= a.len()
    ensures s == sum(a@.map(|k, x| x as int), i as int, j as int)
// </vc-spec>
// <vc-code>
{
    let mut s: i32 = 0;
    let mut k: usize = i;
    
    while k < j
        invariant
            i <= k <= j,
            j <= a.len(),
            s as int == sum(a@.map(|idx: int, x: i32| x as int), i as int, k as int),
        decreases j - k
    {
        let old_s = s;
        let old_k = k;
        
        proof {
            let a_seq = a@.map(|idx: int, x: i32| x as int);
            sum_extend(a_seq, i as int, k as int);
            assert(a_seq[k as int] == a@[k as int] as int);
            assert(sum(a_seq, i as int, (k + 1) as int) == sum(a_seq, i as int, k as int) + a_seq[k as int]);
        }
        
        s = (s as i64 + a[k] as i64) as i32;
        k = k + 1;
        
        proof {
            let a_seq = a@.map(|idx: int, x: i32| x as int);
            assert(old_s as int == sum(a_seq, i as int, old_k as int));
            assert(s as int == old_s as int + a@[old_k as int] as int);
            assert(s as int == sum(a_seq, i as int, old_k as int) + a_seq[old_k as int]);
            assert(s as int == sum(a_seq, i as int, (old_k + 1) as int));
            assert(k == old_k + 1);
            assert(s as int == sum(a_seq, i as int, k as int));
        }
    }
    
    s
}
// </vc-code>

fn main() {}

}