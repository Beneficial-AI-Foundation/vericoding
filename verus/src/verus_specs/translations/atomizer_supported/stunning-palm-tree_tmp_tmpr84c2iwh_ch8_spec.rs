use vstd::prelude::*;

verus! {

pub enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> }
}

pub spec fn Length<T>(xs: List<T>) -> int
    ensures Length(xs) >= 0
{
    match xs {
        List::Nil => 0,
        List::Cons { head: _, tail } => 1 + Length(*tail)
    }
}

pub spec fn At<T>(xs: List<T>, i: nat) -> T
    requires i < Length(xs)
{
    if i == 0 { xs->head } else { At(*xs->tail, i - 1) }
}

pub spec fn Ordered(xs: List<int>) -> bool {
    match xs {
        List::Nil => true,
        List::Cons { head: _, tail: box List::Nil } => true,
        List::Cons { head: hd0, tail: box List::Cons { head: hd1, tail: _ } } => (hd0 <= hd1) && Ordered(*xs->tail)
    }
}

pub proof fn AllOrdered(xs: List<int>, i: nat, j: nat)
    requires(Ordered(xs) && i <= j < Length(xs))
    ensures(At(xs, i) <= At(xs, j))
{
}

pub spec fn Count<T>(xs: List<T>, p: T) -> int
    ensures Count(xs, p) >= 0
{
    match xs {
        List::Nil => 0,
        List::Cons { head: hd, tail: tl } => (if hd == p { 1 } else { 0 }) + Count(*tl, p)
    }
}

pub spec fn Project<T>(xs: List<T>, p: T) -> List<T> {
    match xs {
        List::Nil => List::Nil,
        List::Cons { head: hd, tail: tl } => if hd == p { List::Cons { head: hd, tail: box Project(*tl, p) } } else { Project(*tl, p) }
    }
}

pub proof fn CountProject<T>(xs: List<T>, ys: List<T>, p: T)
    requires(Project(xs, p) == Project(ys, p))
    ensures(Count(xs, p) == Count(ys, p))
{
}

pub spec fn InsertionSort(xs: List<int>) -> List<int>
{
    match xs {
        List::Nil => List::Nil,
        List::Cons { head: x, tail: rest } => Insert(x, InsertionSort(*rest))
    }
}

pub spec fn Insert(x: int, xs: List<int>) -> List<int>
{
    match xs {
        List::Nil => List::Cons { head: x, tail: box List::Nil },
        List::Cons { head: hd, tail: tl } => if x < hd { List::Cons { head: x, tail: box xs } } else { List::Cons { head: hd, tail: box Insert(x, *tl) } }
    }
}

pub proof fn InsertionSortOrdered(xs: List<int>)
    ensures(Ordered(InsertionSort(xs)))
{
}

pub proof fn InsertOrdered(y: int, xs: List<int>)
    requires(Ordered(xs))
    ensures(Ordered(Insert(y, xs)))
{
}

pub proof fn InsertionSortSameElements(xs: List<int>, p: int)
    ensures(Project(xs, p) == Project(InsertionSort(xs), p))
{
}

pub proof fn InsertSameElements(y: int, xs: List<int>, p: int)
    ensures(Project(List::Cons { head: y, tail: box xs }, p) == Project(Insert(y, xs), p))
{
}

}