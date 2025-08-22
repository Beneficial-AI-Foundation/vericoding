//IMPL 
method IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1])
{
  result := true;
  var i := 0;
  
  while i < |x| / 2
    invariant 0 <= i <= |x| / 2
    invariant result <==> (forall j :: 0 <= j < i ==> x[j] == x[|x| - j - 1])
  {
    if x[i] != x[|x| - i - 1] {
      result := false;
      return;
    }
    i := i + 1;
  }
}