//ATOM


datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//ATOM
method Max (x: nat, y:nat) returns (r:nat)
  ensures (r >= x && r >=y)
  ensures (r == x || r == y)
{
  /* code modified by LLM (iteration 1): Fixed implementation to properly compute maximum and satisfy postconditions */
  if x >= y {
    r := x;
  } else {
    r := y;
  }
}


//IMPL 

method Test ()
{
}