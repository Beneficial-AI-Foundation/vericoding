//IMPL
method IsNonPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> (exists k :: 2 <= k < n && n % k == 0)
{
  var i := 2;
  result := false;
  
  while i < n
    invariant 2 <= i <= n
    invariant result <==> (exists k :: 2 <= k < i && n % k == 0)
  {
    if n % i == 0 {
      result := true;
      return;
    }
    i := i + 1;
  }
}