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
  /* code modified by LLM (iteration 1): Fixed compilation errors - removed invalid syntax and implemented proper array to list conversion */
  l := Nil;
  var idx := a.Length;
  
  while idx > 0
    invariant 0 <= idx <= a.Length
    invariant length(l) == a.Length - idx
    invariant forall i: int :: idx <= i < a.Length ==> at(l, i - idx) == a[i]
    invariant forall x :: mem(l, x) ==> exists i: int :: idx <= i < a.Length && a[i] == x
    decreases idx
  {
    idx := idx - 1;
    l := Cons(a[idx], l);
  }
}

//IMPL 

method Main() {
 /* code modified by LLM (iteration 1): Fixed constructor syntax and implemented proper main method */
 var l: List<int> := Cons(1, Cons(2, Cons(3, Nil)));
 var arr: array<int> := new int[3](i => i + 1);
 var t: List<int> := from_array(arr);
 print l;
 print "\n";
 print t;
 print "\n";
 print t == l;
}