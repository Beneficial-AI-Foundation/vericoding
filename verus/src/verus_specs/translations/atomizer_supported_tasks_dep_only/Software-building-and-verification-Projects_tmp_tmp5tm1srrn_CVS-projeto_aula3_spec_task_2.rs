use vstd::prelude::*;

verus! {

pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

pub open spec fn add(l: List<int>) -> int {
    match l {
        List::Nil => 0,
        List::Cons(x, xs) => x + add(*xs),
    }
}

pub fn addImp(l: List<int>) -> (r: int)
    ensures r == add(l)
{
}

}