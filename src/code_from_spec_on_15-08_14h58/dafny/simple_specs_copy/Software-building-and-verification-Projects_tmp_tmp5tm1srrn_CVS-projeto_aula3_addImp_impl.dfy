//ATOM

// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//ATOM

function add(l : List<int>) : int {
 match l
 case Nil => 0
 case Cons(x,xs) => x + add(xs)
}


//IMPL addImp

method addImp(l : List<int>) returns (r: int)
 ensures r == add(l)
{
    r := 0;
    var current := l;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while current != Nil
        invariant r + add(current) == add(l)
        decreases current
    {
        match current {
            case Cons(head, tail) =>
                r := r + head;
                current := tail;
        }
    }
}