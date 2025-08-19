//ATOM

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM

function add(l:List<int>) : int
{
  match l
  case Nil => 0
  case Cons(x, xs) => x + add(xs)
}


// SPEC


method addImp (l: List<int>) returns (s: int)
  ensures s == add(l)
{
}