use vstd::prelude::*;

verus! {

pub enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> }
}

pub spec fn append<T>(xs: List<T>, ys: List<T>) -> List<T> {
    match xs {
        List::Nil => ys,
        List::Cons { head: x, tail: xs_prime } => List::Cons { head: x, tail: Box::new(append(*xs_prime, ys)) }
    }
}

pub proof fn AppendNil<T>(xs: List<T>)
    ensures append(xs, List::Nil) == xs
{
}

pub proof fn AppendAssoc<T>(xs: List<T>, ys: List<T>, zs: List<T>)
    ensures append(append(xs, ys), zs) == append(xs, append(ys, zs))
{
}

pub spec fn Return<T>(a: T) -> List<T> {
    List::Cons { head: a, tail: Box::new(List::Nil) }
}

pub spec fn Bind<T, U>(xs: List<T>, f: spec_fn(T) -> List<U>) -> List<U> {
    match xs {
        List::Nil => List::Nil,
        List::Cons { head: x, tail: xs_prime } => append(f(x), Bind(*xs_prime, f))
    }
}

pub proof fn LeftIdentity<T>(a: T, f: spec_fn(T) -> List<T>)
    ensures Bind(Return(a), f) == f(a)
{
}

pub proof fn RightIdentity<T>(m: List<T>)
    ensures Bind(m, Return) == m
{
}

pub proof fn Associativity<T>(m: List<T>, f: spec_fn(T) -> List<T>, g: spec_fn(T) -> List<T>)
    ensures Bind(Bind(m, f), g) == Bind(m, |x: T| Bind(f(x), g))
{
}

pub proof fn BindOverAppend<T>(xs: List<T>, ys: List<T>, g: spec_fn(T) -> List<T>)
    ensures Bind(append(xs, ys), g) == append(Bind(xs, g), Bind(ys, g))
{
}

}