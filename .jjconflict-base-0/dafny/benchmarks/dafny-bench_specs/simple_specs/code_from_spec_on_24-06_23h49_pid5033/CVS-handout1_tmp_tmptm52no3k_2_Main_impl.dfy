//ATOM
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

//ATOM
method from_array<T>(a: array<T>) returns (l: List<T>)
 requires a.Length >= 0
 ensures length(l) == a.Length
 ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
 ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{
  /* code modified by LLM (iteration 1): Fixed from_array implementation to properly convert array to list */
  l := Nil;
  var idx := 0;
  while idx < a.Length
    invariant 0 <= idx <= a.Length
    invariant length(l) == idx
    invariant forall i: int :: 0 <= i < length(l) ==> at(l, length(l) - 1 - i) == a[idx - 1 - i]
    invariant forall x :: mem(l, x) ==> exists i: int :: 0 <= i < idx && a[i] == x
    decreases a.Length - idx
  {
    l := Cons(a[idx], l);
    idx := idx + 1;
  }
  
  // Reverse the list to match the array order
  var reversed := Nil;
  var temp := l;
  while temp != Nil
    invariant length(reversed) + length(temp) == a.Length
    decreases length(temp)
  {
    reversed := Cons(temp.head, reversed);
    temp := temp.tail;
  }
  l := reversed;
}

//IMPL 
method Main() {
 /* code modified by LLM (iteration 1): Fixed datatype constructor references and array initialization syntax */
 var l: List<int> := Cons(1, Cons(2, Cons(3, Nil)));
 var arr: array<int> := new int[3];
 arr[0] := 1;
 arr[1] := 2;
 arr[2] := 3;
 var t: List<int> := from_array(arr);
 print l;
 print "\n";
 print t;
 print "\n";
 print t == l;
}