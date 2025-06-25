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
    match l
    case Nil => 
        r := 0;
    case Cons(x, xs) =>
        var tail_sum := addImp(xs);
        r := x + tail_sum;
}