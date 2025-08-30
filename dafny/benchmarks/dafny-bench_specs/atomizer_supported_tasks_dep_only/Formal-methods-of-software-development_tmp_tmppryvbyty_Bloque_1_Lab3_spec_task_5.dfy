
//ATOM_PLACEHOLDER_multipleReturns//ATOM_PLACEHOLDER_multipleReturns2//ATOM_PLACEHOLDER_multipleReturns3// ATOM 

function factorial(n:int):int
requires n>=0
{
    if n==0 || n==1 then 1 else n*factorial(n-1)
}


// PROGRAMA VERIFICADOR DE WHILE
//ATOM_PLACEHOLDER_ComputeFact

// SPEC 

method ComputeFact2 (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{
}



// n>=1 ==> 1 + 3 + 5 + ... + (2*n-1) = n*n

//ATOM_PLACEHOLDER_Sqare


//ATOM_PLACEHOLDER_sumSerie

//ATOM_PLACEHOLDER_unknown_1152 Sqare_Lemma (n:int)
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


//ATOM_PLACEHOLDER_Sqare2





