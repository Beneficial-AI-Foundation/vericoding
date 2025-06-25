enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

spec fn length<T>(l: List<T>) -> nat {
    match l {
        List::Nil => 0,
        List::Cons(_, t) => 1 + length(*t),
    }
}

spec fn mem<T>(l: List<T>, x: T) -> bool {
    match l {
        List::Nil => false,
        List::Cons(h, t) => if h == x { true } else { mem(*t, x) },
    }
}

spec fn at<T>(l: List<T>, i: nat) -> T
    recommends i < length(l)
{
    if i == 0 { l->Cons_0 } else { at(l->Cons_1, (i - 1) as nat) }
}

pub fn from_array<T>(a: &[T]) -> (l: List<T>)
    requires a.len() >= 0
    ensures length(l) == a.len()
    ensures forall|i: int| 0 <= i < length(l) ==> at(l, i as nat) == a[i as usize]
    ensures forall|x| mem(l, x) ==> exists|i: int| 0 <= i < length(l) && a[i as usize] == x
{
}