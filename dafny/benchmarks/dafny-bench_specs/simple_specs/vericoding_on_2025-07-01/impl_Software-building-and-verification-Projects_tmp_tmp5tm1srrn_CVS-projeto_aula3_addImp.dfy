//ATOM

// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//ATOM

function add(l : List<int>) : int {
 match l
 case Nil => 0
 case Cons(x,xs) => x + add(xs)
}


//IMPL

method addImp(l : List<int>) returns (r: int)
 ensures r == add(l)
{
    r := 0;
    var current := l;
    
    while current != Nil
        invariant r + add(current) == add(l)
    {
        match current {
            case Cons(head, tail) =>
                r := r + head;
                current := tail;
        }
    }
}