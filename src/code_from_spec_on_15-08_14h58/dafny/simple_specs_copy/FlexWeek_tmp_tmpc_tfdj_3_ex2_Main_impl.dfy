//ATOM
// 2. Given an array of positive and negative integers, it returns an array of the absolute value of all the integers. [-4,1,5,-2,-5]->[4,1,5,2,5]

function abs(a:int):nat
{
  if a < 0 then -a else a
}


//ATOM

method aba(a:array<int>)returns (b:array<int>)
ensures a.Length == b.Length // needed for next line
ensures forall x :: 0<=x<b.Length ==> b[x] == abs(a[x])
{
  b := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> b[k] == abs(a[k])
  {
    b[i] := abs(a[i]);
    i := i + 1;
  }
}


//IMPL Main

method Main()
{
 /* code modified by LLM (iteration 1): fixed array initialization syntax */
 var a := new int[4](i => if i == 0 then 1 else if i == 1 then -2 else if i == 2 then -2 else 1);
 var b := aba(a);
 
}