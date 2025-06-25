use vstd::prelude::*;

verus! {

pub enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> }
}

pub open spec fn length<T>(l: List<T>) -> nat {
    match l {
        List::Nil => 0,
        List::Cons { head: _, tail } => 1 + length(*tail)
    }
}

pub open spec fn mem<T>(l: List<T>, x: T) -> bool {
    match l {
        List::Nil => false,
        List::Cons { head: h, tail: t } => if h == x { true } else { mem(*t, x) }
    }
}

pub open spec fn at<T>(l: List<T>, i: nat) -> T
    recommends i < length(l)
{
    if i == 0 { l->head } else { at(*l->tail, (i - 1) as nat) }
}

pub fn from_array<T>(a: &[T]) -> (l: List<T>)
    requires
        a.len() >= 0,
    ensures
        length(l) == a.len(),
        forall|i: int| 0 <= i < length(l) ==> at(l, i as nat) == a[i as usize],
        forall|x: T| mem(l, x) ==> exists|i: int| 0 <= i < length(l) && a[i as usize] == x,
{
}

pub fn Main() {
}

}