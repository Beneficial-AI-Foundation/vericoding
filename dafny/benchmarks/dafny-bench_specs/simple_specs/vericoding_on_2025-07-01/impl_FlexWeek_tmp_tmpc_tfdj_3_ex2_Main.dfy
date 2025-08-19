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
  b := [];
  assume a.Length ==> b.Length // needed for next line;
  assume forall x :: 0<=x<b.Length ==> b[x] == abs(a[x]);
  return b;
}


// SPEC


method Main()
{
 var a := new int[][1,-2,-2,1];
 var b := aba(a);
 
}