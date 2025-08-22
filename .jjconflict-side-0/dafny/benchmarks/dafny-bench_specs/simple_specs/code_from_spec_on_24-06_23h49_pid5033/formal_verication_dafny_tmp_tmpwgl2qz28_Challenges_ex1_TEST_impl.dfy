//ATOM
// ex3errors.dfy in Assignment 1
// verify that an array of characters is a Palindrome



method PalVerify(a: array<char>) returns (yn: bool)
ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j]) 
{
  yn := false;
  assume yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1];
  assume yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1];
  assume forall j :: 0<=j<a.Length ==> a[j] == old(a[j]);
  return yn;
}


//IMPL SPEC

method TEST()
{
}