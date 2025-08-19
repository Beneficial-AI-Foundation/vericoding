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

//IMPL from_array

/* code modified by LLM (iteration 1): Fixed loop invariant to correctly maintain membership property */
method from_array<T>(a: array<T>) returns (l: List<T>)
 requires a.Length >= 0
 ensures length(l) == a.Length
 ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
 ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{
  l := Nil;
  var j := a.Length;
  while j > 0
    invariant 0 <= j <= a.Length
    invariant length(l) == a.Length - j
    invariant forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[j + i]
    invariant forall x :: mem(l, x) ==> exists i: int :: j <= i < a.Length && a[i] == x
    invariant forall i: int :: j <= i < a.Length ==> exists k: int :: 0 <= k < length(l) && at(l, k) == a[i]
    decreases j
  {
    j := j - 1;
    l := Cons(a[j], l);
  }
}

//IMPL Main

method Main() {
 var l: List<int> := List.Cons(1, List.Cons(2, List.Cons(3, Nil)));
 var arr: array<int> := new int [3](i => i + 1);
 var t: List<int> := from_array(arr);
 print l;
 print "\n";
 print t;
 print "\n";
 print t == l;
}