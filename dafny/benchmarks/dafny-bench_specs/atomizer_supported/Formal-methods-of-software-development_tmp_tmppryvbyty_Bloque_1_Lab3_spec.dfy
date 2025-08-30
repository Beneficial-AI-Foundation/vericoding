
// SPEC 

method multipleReturns (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures less < x < more
// SPEC 


method multipleReturns2 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more + less == 2*x
// SPEC 

// TODO: Hacer en casa
method multipleReturns3 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more - less == 2*y
// ATOM 

function factorial(n:int):int
requires n>=0
{
    if n==0 || n==1 then 1 else n*factorial(n-1)
}


// PROGRAMA VERIFICADOR DE WHILE
// SPEC 

// PROGRAMA VERIFICADOR DE WHILE
method ComputeFact (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)

{
}


// SPEC 

method ComputeFact2 (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{
}



// n>=1 ==> 1 + 3 + 5 + ... + (2*n-1) = n*n

// SPEC 


// n>=1 ==> 1 + 3 + 5 + ... + (2*n-1) = n*n

method Sqare(a:int) returns (x:int)
requires a>=1
ensures x == a*a
{
}



// ATOM 


function sumSerie(n:int):int
requires n >=1 
{
    if n==1 then 1 else sumSerie(n-1) + 2*n -1
}


 Sqare_Lemma (n:int)
requires n>=1
ensures sumSerie(n) == n*n
{
    if n==1 {}
    else{
        Sqare_Lemma(n-1);

        calc == {
            sumSerie(n);
            sumSerie(n-1) + 2*n -1;
            {
                Sqare_Lemma(n-1);
            }
            (n-1)*(n-1) + 2*n -1;
            n*n-2*n+1 +2*n -1;
            n*n;
        }
    }
}


// SPEC 


method Sqare2(a:int) returns (x:int)
requires a>=1
ensures x == a*a

{
}






