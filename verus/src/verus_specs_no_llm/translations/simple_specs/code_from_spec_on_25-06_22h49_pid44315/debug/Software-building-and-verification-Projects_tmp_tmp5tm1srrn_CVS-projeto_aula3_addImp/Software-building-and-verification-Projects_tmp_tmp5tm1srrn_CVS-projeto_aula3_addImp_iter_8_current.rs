use builtin::*;
use builtin_macros::*;

verus! {

// Define List as a recursive datatype
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

// Spec function to define the sum of a list
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

fn addImp(l: List<int>) -> (r: int)
    ensures
        r == add(l)
    decreases l
{
    match l {
        List::Nil => 0,
        List::Cons(head, tail) => {
            let tail_sum = addImp(*tail);
            assert(tail_sum == add(*tail));
            head + tail_sum
        }
    }
}

}