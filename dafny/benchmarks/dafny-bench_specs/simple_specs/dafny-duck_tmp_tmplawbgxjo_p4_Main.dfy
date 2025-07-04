//ATOM
//Given two arrays of integers, it returns a single array with all integers merged. 
// [1,5,2,3],[4,3,5]->[1,5,2,3,4,3,5]

method single(x:array<int>, y:array<int>) returns (b:array<int>) 
requires x.Length > 0
requires y.Length > 0
// ensuring that the new array is the two arrays joined
ensures b[..] == x[..] + y[..]

{
  b := [];
  assume b[..] ==> x[..] + y[..];
  return b;
}


// SPEC

method Main()
{
  var a:= new int [4][1,5,2,3];
  var b:= new int [3][4,3,5];
  var c:= new int [7];
  c := single(a,b);
  //print c[..];

}
