datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM
function add(l:List<int>) : int
{
  match l
  case Nil => 0
  case Cons(x, xs) => x + add(xs)
}

//IMPL addImp
method addImp (l: List<int>) returns (s: int)
  ensures s == add(l)
{
  s := 0;
  var current := l;
  
  /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
  while current != Nil
    invariant s + add(current) == add(l)
    decreases current
  {
    match current {
      case Cons(head, tail) =>
        s := s + head;
        current := tail;
    }
  }
}