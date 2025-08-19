//IMPL 
method ContainsZ(s: string) returns (result: bool)
  ensures result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'))
{
  result := false;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result <==> (exists j :: 0 <= j < i && (s[j] == 'z' || s[j] == 'Z'))
  {
    if s[i] == 'z' || s[i] == 'Z' {
      result := true;
      return;
    }
    i := i + 1;
  }
}