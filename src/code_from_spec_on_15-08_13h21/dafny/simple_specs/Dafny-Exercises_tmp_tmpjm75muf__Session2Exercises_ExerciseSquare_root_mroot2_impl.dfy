//IMPL 
method mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r := 0;
    while (r+1)*(r+1) <= n
        invariant r >= 0
        invariant r*r <= n
    {
        r := r + 1;
    }
}