//ATOM
function has_count(v: int, a: array<int>, n: int): int
  reads a // This allows the function to read from array 'a'
  requires n >= 0 && n <= a.Length
{
  if n == 0 then 0 else
  (if a[n-1] == v then has_count(v, a, n-1) + 1 else has_count(v, a, n-1))
}

//IMPL 
method count (v: int, a: array<int>, n: int) returns (r: int)
  requires n >= 0 && n <= a.Length
  ensures has_count(v, a, n) == r
{
  /* code modified by LLM (iteration 1): Changed to iterate backwards from n to 0 to match the recursive structure of has_count, making the loop invariant easier to maintain */
  r := 0;
  var i := n;
  while i > 0
    invariant 0 <= i <= n
    invariant r == has_count(v, a, n) - has_count(v, a, i)
  {
    i := i - 1;
    if a[i] == v {
      r := r + 1;
    }
  }
}