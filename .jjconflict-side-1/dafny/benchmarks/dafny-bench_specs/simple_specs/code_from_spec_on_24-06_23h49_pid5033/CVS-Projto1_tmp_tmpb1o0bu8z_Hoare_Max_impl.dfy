//ATOM


datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//IMPL Max
method Max (x: nat, y:nat) returns (r:nat)
  ensures (r >= x && r >=y)
  ensures (r == x || r == y)
{
  if x >= y {
    r := x;
  } else {
    r := y;
  }
}