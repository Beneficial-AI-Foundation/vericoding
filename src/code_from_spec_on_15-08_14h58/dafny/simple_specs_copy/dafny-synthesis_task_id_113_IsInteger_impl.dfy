//ATOM
predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

//IMPL 
method IsInteger(s: string) returns (result: bool)
  ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
{
  if |s| == 0 {
    result := false;
    return;
  }
  
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> IsDigit(s[j])
  {
    if !IsDigit(s[i]) {
      result := false;
      return;
    }
    i := i + 1;
  }
  
  result := true;
}