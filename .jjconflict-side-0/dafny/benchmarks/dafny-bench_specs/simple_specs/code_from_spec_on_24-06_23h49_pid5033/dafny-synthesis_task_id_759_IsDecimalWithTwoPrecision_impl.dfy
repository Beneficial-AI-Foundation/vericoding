//IMPL 
method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
  ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
  ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
{
  result := false;
  
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant !result ==> forall j :: 0 <= j < i ==> !(s[j] == '.' && |s| - j - 1 == 2)
  {
    if s[i] == '.' && |s| - i - 1 == 2 {
      result := true;
      return;
    }
    i := i + 1;
  }
}