pub fn from_array<T>(a: &[T]) -> List<T>
    requires(
        true
    )
    ensures(|l: List<T>|
        forall|i: int| 0 <= i < a.len() ==> mem(a[i], l) &&
        forall|x: T| mem(x, l) ==> exists|y: int| 0 <= y < a.len() && a[y] == x
    )
{
}

pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

pub fn mem<T>(x: T, l: List<T>) -> bool
where
    T: PartialEq,
{
    match l {
        List::Nil => false,
        List::Cons(h, t) => h == x || mem(x, *t),
    }
}