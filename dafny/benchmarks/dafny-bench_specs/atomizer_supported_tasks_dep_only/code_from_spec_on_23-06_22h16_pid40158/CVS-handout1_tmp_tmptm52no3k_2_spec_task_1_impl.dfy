/*                                      Functional Lists and Imperative Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes        57854
*/

// ATOM List
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

// ATOM 
function length<T>(l: List<T>): nat
{
  match l
  case Nil => 0
  case Cons(_, t) => 1 + length(t)
}

// ATOM 
predicate mem<T(==)> (l: List<T>, x: T)
{
  match l
  case Nil => false
  case Cons(h, t) => if(h == x) then true else mem(t, x)
}

// ATOM 
function at<T>(l: List<T>, i: nat): T
  requires i < length(l)
{
  if i == 0 then l.head else at(l.tail, i - 1)
}

// IMPL from_array
method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length >= 0
  ensures length(l) == a.Length
  ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
  ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{
  l := Nil;
  var i := a.Length;
  
  /* code modified by LLM (iteration 1): Fixed loop invariants to correctly establish the relationship between list positions and array indices */
  while i > 0
    invariant 0 <= i <= a.Length
    invariant length(l) == a.Length - i
    invariant forall j: int :: 0 <= j < length(l) ==> at(l, j) == a[i + j]
    invariant forall x :: mem(l, x) ==> exists k: int :: i <= k < a.Length && a[k] == x
  {
    i := i - 1;
    l := Cons(a[i], l);
  }
}

// ATOM Main
method Main() {
  // Empty main method
}