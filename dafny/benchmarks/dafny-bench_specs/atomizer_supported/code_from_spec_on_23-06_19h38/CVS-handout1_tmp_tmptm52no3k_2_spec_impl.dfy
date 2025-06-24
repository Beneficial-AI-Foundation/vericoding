/*                                      Functional Lists and Imperative Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes        57854
*/

// ATOM 


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

/* code modified by LLM (iteration 1): Added helper function to reverse a list */
function reverse<T>(l: List<T>): List<T>
{
  reverseAcc(l, Nil)
}

/* code modified by LLM (iteration 1): Added accumulator-based reverse function */
function reverseAcc<T>(l: List<T>, acc: List<T>): List<T>
{
  match l
  case Nil => acc
  case Cons(h, t) => reverseAcc(t, Cons(h, acc))
}

/* code modified by LLM (iteration 1): Added lemma about reverse properties */
lemma reverseProperties<T>(l: List<T>)
  ensures length(reverse(l)) == length(l)
  ensures forall i: nat :: i < length(l) ==> at(reverse(l), i) == at(l, length(l) - 1 - i)
{
  reverseAccProperties(l, Nil);
}

/* code modified by LLM (iteration 1): Added lemma about reverseAcc properties */
lemma reverseAccProperties<T>(l: List<T>, acc: List<T>)
  ensures length(reverseAcc(l, acc)) == length(l) + length(acc)
  ensures forall i: nat :: i < length(l) ==> at(reverseAcc(l, acc), i) == at(l, length(l) - 1 - i)
  ensures forall i: nat :: i < length(acc) ==> at(reverseAcc(l, acc), length(l) + i) == at(acc, i)
{
  match l
  case Nil => {}
  case Cons(h, t) => 
    reverseAccProperties(t, Cons(h, acc));
}

method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length >= 0
  ensures length(l) == a.Length
  ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
  ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{
  /* code modified by LLM (iteration 1): Build list in reverse order first, then reverse it */
  var temp := Nil;
  var i := a.Length;
  while i > 0
    invariant 0 <= i <= a.Length
    invariant length(temp) == a.Length - i
    invariant forall j: int :: 0 <= j < length(temp) ==> at(temp, j) == a[a.Length - 1 - j]
    invariant forall x :: mem(temp, x) ==> exists k: int :: i <= k < a.Length && a[k] == x
  {
    i := i - 1;
    temp := Cons(a[i], temp);
  }
  
  /* code modified by LLM (iteration 1): Reverse the temporary list to get correct order */
  l := reverse(temp);
  
  /* code modified by LLM (iteration 1): Apply lemma to establish postconditions */
  reverseProperties(temp);
}


// IMPL Main

method Main() {
}