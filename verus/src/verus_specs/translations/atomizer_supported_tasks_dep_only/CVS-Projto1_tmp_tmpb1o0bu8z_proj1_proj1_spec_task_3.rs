pub fn from_array<T>(a: &[T]) -> List<T>
    requires(a.len() > 0)
    ensures(|l: List<T>| forall|j: usize| 0 <= j < a.len() ==> mem(a[j], l))
{
}

pub fn mem<T: Eq>(x: T, l: List<T>) -> bool
{
    match l {
        List::Nil => false,
        List::Cons(y, r) => if x == y { true } else { mem(x, *r) }
    }
}