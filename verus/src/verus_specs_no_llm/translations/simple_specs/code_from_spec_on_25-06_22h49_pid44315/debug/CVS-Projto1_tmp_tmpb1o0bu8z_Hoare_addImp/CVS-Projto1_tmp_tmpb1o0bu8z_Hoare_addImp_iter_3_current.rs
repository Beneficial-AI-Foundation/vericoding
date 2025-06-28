use builtin::*;
use builtin_macros::*;

verus! {

// Define a simple List enum
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

// Spec function to compute the sum of a list
pub open spec fn add(l: List<int>) -> int 
    decreases l
{
    match l {
        List::Nil => 0,
        List::Cons(head, tail) => head + add(*tail),
    }
}

fn main() {
}

fn addImp(l: List<int>) -> (s: int)
    ensures
        s == add(l)
    decreases l
{
    match l {
        List::Nil => 0,
        List::Cons(head, tail) => {
            let tail_sum = addImp(*tail);
            head + tail_sum
        }
    }
}

}