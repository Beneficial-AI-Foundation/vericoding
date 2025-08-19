datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM

function add(l:List<int>) : int
{
  match l
  case Nil => 0
  case Cons(x, xs) => x + add(xs)
}

//IMPL 

method addImp (l: List<int>) returns (s: int)
  ensures s == add(l)
{
  s := 0;
  var current := l;
  
  /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
  while current != Nil
    invariant s + add(current) == add(l)
    decreases current
  {
    s := s + current.head;
    current := current.tail;
  }
}