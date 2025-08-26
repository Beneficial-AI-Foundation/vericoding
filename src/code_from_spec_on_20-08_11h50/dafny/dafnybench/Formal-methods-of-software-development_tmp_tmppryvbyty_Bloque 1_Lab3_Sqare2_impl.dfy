// PROGRAMA VERIFICADOR DE WHILE



// n>=1 ==> 1 + 3 + 5 + ... + (2*n-1) = n*n



// <vc-spec>
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

// <vc-helpers>
function sumSerieExtended(n:int):int
requires n >= 0
{
    if n == 0 then 0 else sumSerie(n)
}

lemma SumSerieExtendedProperty(n:int)
requires n >= 0
ensures n == 0 ==> sumSerieExtended(n) == 0
ensures n >= 1 ==> sumSerieExtended(n) == sumSerie(n)
{
}
// </vc-helpers>

method Sqare2(a:int) returns (x:int)
requires a>=1
ensures x == a*a
// </vc-spec>
// <vc-code>
{
  var i := 1;
  x := 0;
  
  while i <= a
    invariant 1 <= i <= a + 1
    invariant x == sumSerieExtended(i-1)
  {
    x := x + 2*i - 1;
    i := i + 1;
  }
  
  Sqare_Lemma(a);
}
// </vc-code>