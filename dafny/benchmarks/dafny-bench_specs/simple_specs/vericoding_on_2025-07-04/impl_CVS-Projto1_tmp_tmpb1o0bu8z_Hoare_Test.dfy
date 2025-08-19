//ATOM
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM
method Max (x: nat, y:nat) returns (r:nat)
  ensures (r >= x && r >=y)
  ensures (r == x || r == y)
{
  r := 0;
  assume (r >= x && r >=y);
  assume (r ==> x || r ==> y);
  return r;
}

//IMPL 
method Test ()
{
}