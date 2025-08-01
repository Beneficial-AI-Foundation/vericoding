// Ch. 8: Sorting

// ATOM 
// Ch. 8: Sorting

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
// ATOM 

function Length<T>(xs: List<T>): int
  ensures Length(xs) >= 0
{
    match xs
    case Nil => 0
    case Cons(_, tl) => 1 + Length(tl)
}


// ATOM 

function At<T>(xs: List, i: nat): T
  requires i < Length(xs)
{
    if i == 0 then xs.head else At(xs.tail, i - 1)
}


// ATOM 

ghost predicate Ordered(xs: List<int>) {
    match xs
    case Nil => true
    case Cons(_, Nil) => true
    case Cons(hd0, Cons(hd1, _)) => (hd0 <= hd1) && Ordered(xs.tail)
}


// ATOM 

lemma AllOrdered(xs: List<int>, i: nat, j: nat)
  requires Ordered(xs) && i <= j < Length(xs)
  ensures At(xs, i) <= At(xs, j)
{
    if i != 0 {
        AllOrdered(xs.tail, i - 1, j - 1);
    } else if i == j {
    } else {
        AllOrdered(xs.tail, 0, j - 1);
    }
}


// Ex. 8.0 generalize fron int to T by: T(==)
// ATOM 

// Ex. 8.0 generalize fron int to T by: T(==)
ghost function Count<T(==)>(xs: List<T>, p: T): int
  ensures Count(xs, p) >= 0
{
    match xs
    case Nil => 0
    case Cons(hd, tl) => (if hd == p then 1 else 0) + Count(tl, p)
}


// ATOM 

ghost function Project<T(==)>(xs: List<T>, p: T): List<T> {
    match xs
    case Nil => Nil
    case Cons(hd, tl) => if hd == p then Cons(hd, Project(tl, p)) else Project(tl, p)
}


// Ex 8.1
 CountProject<T(==)>(xs: List<T>, ys: List<T>, p: T)
  requires Project(xs, p) == Project(ys, p)
  ensures Count(xs, p) == Count(ys, p)
{
    match xs
    case Nil => {
        match ys
        case Nil => {}
        case Cons(yhd, ytl) => {
            CountProject(xs, ytl, p);
        }
    }
    case Cons(xhd, xtl) => {
        match ys
        case Nil => {
            CountProject(xtl, ys, p);
        }
        case Cons(yhd, ytl) => {
            if xhd == p && yhd == p {
                CountProject(xtl, ytl, p);
            } else if xhd != p && yhd == p {
                CountProject(xtl, ys, p);
            } else if xhd == p && yhd != p {
                CountProject(xs, ytl, p);
            } else {
                CountProject(xtl, ytl, p);
            }
        }
    }
}

// ATOM 

function InsertionSort(xs: List<int>): List<int>
{
    match xs
    case Nil => Nil
    case Cons(x, rest) => Insert(x, InsertionSort(rest))
}


// ATOM 

function Insert(x: int, xs: List<int>): List<int>
{
    match xs
    case Nil => Cons(x, Nil)
    case Cons(hd, tl) => if x < hd then Cons(x, xs) else Cons(hd, Insert(x, tl))
}


// ATOM 

lemma InsertionSortOrdered(xs: List<int>)
  ensures Ordered(InsertionSort(xs))
{
    match xs
    case Nil =>
    case Cons(hd, tl) => {
        InsertionSortOrdered(tl);
        InsertOrdered(hd, InsertionSort(tl));
    }
}


// ATOM 

lemma InsertOrdered(y: int, xs: List<int>)
  requires Ordered(xs)
  ensures Ordered(Insert(y, xs))
{
    match xs
    case Nil =>
    case Cons(hd, tl) => {
        if y < hd {
        } else {
            InsertOrdered(y, tl);
        }
    }
}


// ATOM 

lemma InsertionSortSameElements(xs: List<int>, p: int)
  ensures Project(xs, p) == Project(InsertionSort(xs), p)
{
    match xs
    case Nil =>
    case Cons(hd, tl) => {
        InsertSameElements(hd, InsertionSort(tl), p);
    }
}


// ATOM 

lemma InsertSameElements(y: int, xs: List<int>, p: int)
  ensures Project(Cons(y, xs), p) == Project(Insert(y, xs), p)
{}


