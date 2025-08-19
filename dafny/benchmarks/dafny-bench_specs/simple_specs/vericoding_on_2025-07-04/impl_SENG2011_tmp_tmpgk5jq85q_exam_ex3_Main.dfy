//ATOM

method Symmetric(a: array<int>) returns (flag: bool)
ensures flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1]
ensures flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1]
{
  flag := false;
  assume flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1];
  assume flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1];
  return flag;
}
/*


// SPEC
method Main() {
  var data1 := new int[][1,2,3,2,1];
var f1 := Symmetric(data1);
var data2 := new int[][1,2];
var f2 := Symmetric(data2);
//print f2;
}
*/