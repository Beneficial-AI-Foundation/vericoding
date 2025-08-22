//IMPL 
method isPalindrome(s: array<char>) returns (result: bool)
  requires 1<= s.Length <= 200000
  ensures result <==> (forall i:: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
{
  var i := 0;
  result := true;
  
  while i < s.Length / 2
    invariant 0 <= i <= s.Length / 2
    invariant result <==> (forall j :: 0 <= j < i ==> s[j] == s[s.Length - 1 - j])
  {
    if s[i] != s[s.Length - 1 - i] {
      result := false;
      return;
    }
    i := i + 1;
  }
}