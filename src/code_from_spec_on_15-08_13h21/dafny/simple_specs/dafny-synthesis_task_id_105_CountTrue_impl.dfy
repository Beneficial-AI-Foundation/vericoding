//ATOM
/* code modified by LLM (iteration 1): removed redundant null check on non-nullable array type */
function countTo( a:array<bool>, n:int ) : int
 requires 0 <= n && n <= a.Length
 reads a
{
 if (n == 0) then 0 else countTo(a, n-1) + (if a[n-1] then 1 else 0)
}

//IMPL 
/* code modified by LLM (iteration 1): removed redundant null check on non-nullable array type */
method CountTrue(a: array<bool>) returns (result: int)
  ensures result == countTo(a, a.Length)
{
  result := 0;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == countTo(a, i)
  {
    if a[i] {
      result := result + 1;
    }
    i := i + 1;
  }
}