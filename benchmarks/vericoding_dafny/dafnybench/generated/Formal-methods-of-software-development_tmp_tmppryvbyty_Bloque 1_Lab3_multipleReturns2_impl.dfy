function sumSerie(n:int):int
requires n >=1 
{
    if n==1 then 1 else sumSerie(n-1) + 2*n -1
}

// <vc-helpers>
// </vc-helpers>

method multipleReturns2 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more + less == 2*x
// </vc-spec>
// <vc-code>
{
  more := x + y;
  less := x - y;
}
// </vc-code>

lemma Sqare_Lemma (n:int)
requires n>=1
ensures sumSerie(n) == n*n
{
    if n==1 {}
    else{
        Sqare_Lemma(n-1);
        assert sumSerie(n-1) ==(n-1)*(n-1);

        calc == {
            sumSerie(n);
            sumSerie(n-1) + 2*n -1;
            {
                Sqare_Lemma(n-1);
                assert sumSerie(n-1) ==(n-1)*(n-1);
            }
            (n-1)*(n-1) + 2*n -1;
            n*n-2*n+1 +2*n -1;
            n*n;
        }
    assert sumSerie(n) == n*n;
    }
}