
//ATOM_PLACEHOLDER_multipleReturns//ATOM_PLACEHOLDER_multipleReturns2// SPEC 

// TODO: Hacer en casa
method multipleReturns3 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more - less == 2*y
//ATOM_PLACEHOLDER_factorial

// PROGRAMA VERIFICADOR DE WHILE
//ATOM_PLACEHOLDER_ComputeFact

//ATOM_PLACEHOLDER_ComputeFact2


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





