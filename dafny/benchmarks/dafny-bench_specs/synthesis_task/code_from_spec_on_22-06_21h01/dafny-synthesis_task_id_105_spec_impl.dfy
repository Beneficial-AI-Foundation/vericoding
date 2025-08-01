// ATOM
function countTo( a:array<bool>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{
  if (n == 0) then 0 else countTo(a, n-1) + (if a[n-1] then 1 else 0)
}

//IMPL CountTrue
method CountTrue(a: array<bool>) returns (result: int)
    requires a != null
    ensures result == countTo(a, a.Length)
{
    result := 0;
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result == countTo(a, i)
    {
        /* code modified by LLM (iteration 1): Added assertion to help Dafny prove the invariant maintenance */
        assert result == countTo(a, i);
        assert countTo(a, i+1) == countTo(a, i) + (if a[i] then 1 else 0);
        
        if a[i] {
            result := result + 1;
        }
        i := i + 1;
        
        /* code modified by LLM (iteration 1): Added assertion to verify invariant after update */
        assert result == countTo(a, i);
    }
}