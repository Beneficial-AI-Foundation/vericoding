// <vc-preamble>
// PROGRAMA VERIFICADOR DE WHILE



// n>=1 ==> 1 + 3 + 5 + ... + (2*n-1) = n*n



function sumSerie(n:int):int
requires n >=1 
{
    if n==1 then 1 else sumSerie(n-1) + 2*n -1
}

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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Sqare2(a:int) returns (x:int)
requires a>=1
ensures x == a*a
// </vc-spec>
// <vc-code>
{
    assert 1 <= 1 <= a && 1==1*1;
    var y:=1;
    assert 1 <= y <= a && 1==y*y;
    x:=1;
    assert 1 <= y <= a && x==y*y;
    while y < a 
        invariant 1 <= y <= a
        invariant x==y*y
        decreases a - y
    {
        assert 1 <= (y+1) <= a && (x+2*(y+1)-1)==(y+1)*(y+1);
        y:= y+1;
        assert 1 <= y <= a && (x+2*y-1)==y*y;
        x:= x +2*y -1;
        assert 1 <= y <= a && x==y*y;
    }
    assert 1 <= y <= a && x==y*y;
}
// </vc-code>
