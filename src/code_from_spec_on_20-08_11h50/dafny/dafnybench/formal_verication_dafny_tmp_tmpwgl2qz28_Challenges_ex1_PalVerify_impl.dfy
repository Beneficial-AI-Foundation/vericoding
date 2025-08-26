method PalVerify(a: array<int>) returns (yn: bool)
  ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i - 1]
  ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i - 1]
{
  if a.Length <= 1 {
    return true;
  }
  
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall j :: 0 <= j < i ==> a[j] == a[a.Length - j - 1]
  {
    if a[i] != a[a.Length - i - 1] {
      return false;
    }
    i := i + 1;
  }
  
  return true;
}