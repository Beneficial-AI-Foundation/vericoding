/*                                      Functional Lists and Imperative Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes        57854
*/

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM 
function length<T>(l: List<T>): nat
{
  match l
  case Nil => 0
  case Cons(_, t) => 1 + length(t)
}

//ATOM 
predicate mem<T(==)> (l: List<T>, x: T)
{
  match l
  case Nil => false
  case Cons(h, t) => if(h == x) then true else mem(t, x)
}

//ATOM 
function at<T>(l: List<T>, i: nat): T
  requires i < length(l)
{
  if i == 0 then l.head else at(l.tail, i - 1)
}

//IMPL from_array
method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length >= 0
  ensures length(l) == a.Length
  ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
  ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{
  l := Nil;
  var k := 0;
  /* code modified by LLM (iteration 1): Changed algorithm to build list from left to right to match postcondition requirement */
  while k < a.Length
    invariant 0 <= k <= a.Length
    invariant length(l) == k
    /* code modified by LLM (iteration 1): Corrected invariant to properly map list positions to array indices when building left to right */
    invariant forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
    /* code modified by LLM (iteration 1): Fixed membership invariant to relate to processed array elements */
    invariant forall x :: mem(l, x) ==> exists i: int :: 0 <= i < k && a[i] == x
  {
    /* code modified by LLM (iteration 1): Added helper function call to append element at the end */
    l := append_element(l, a[k]);
    k := k + 1;
  }
}

/* code modified by LLM (iteration 2): Added decreases clause to fix termination issue */
function append_element<T>(l: List<T>, x: T): List<T>
  ensures length(append_element(l, x)) == length(l) + 1
  ensures forall i: int :: 0 <= i < length(l) ==> at(append_element(l, x), i) == at(l, i)
  ensures at(append_element(l, x), length(l)) == x
  ensures forall y :: mem(append_element(l, x), y) <==> (mem(l, y) || y == x)
  decreases l
{
  match l
  case Nil => Cons(x, Nil)
  case Cons(h, t) => Cons(h, append_element(t, x))
}

//IMPL Main
method Main() {
}