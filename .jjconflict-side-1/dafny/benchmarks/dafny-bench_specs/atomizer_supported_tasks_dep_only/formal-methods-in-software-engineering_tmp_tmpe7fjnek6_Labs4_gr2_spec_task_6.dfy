/*
Dafny include 2 limbaje:
    * un limbaj pentru specificare 
        MSFOL (ce am discutat până acum)
        adnotări care să ajute în procesul de verificare
    * un limbaj pentru scris programe
*/

// Exemplu de program

//ATOM_PLACEHOLDER_SqrSum

//ATOM_PLACEHOLDER_DivMod

/*
    triple Hoare (| P |) S (| Q |) 
*/

// varianta assume-assert
//ATOM_PLACEHOLDER_HoareTripleAssmAssrt

// varianta requires-ensures

//ATOM_PLACEHOLDER_HoareTripleReqEns

/*
regula pentru while
*/

// varianta cu assert
/*
//ATOM_PLACEHOLDER_WhileRule
*/

// varianta cu invariant
// SPEC 

// varianta cu invariant
method Invariant1()
{
}


//specificarea sumei de patrate
//ATOM_PLACEHOLDER_SqrSumRec
/*
//ATOM_PLACEHOLDER_SqrSum1
*/

// verificarea programului pentru suma de patrate

//ATOM_PLACEHOLDER_SqrSum1

// SqrSumRec(n) = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
least lemma L1(n: int)
	requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
    //OK
}

/*
//ATOM_PLACEHOLDER_SqrSumBy6

inductive lemma L(n: int) // it takes a while
	requires n >= 0
	ensures  SqrSumBy6(n) == 6 * SqrSumRec(n)
{
	if (n == 0) {}
	else {
		L(n-1);
	  	calc == {
			n*((n-1)*(2*n - 1));
			n*(2*n*(n-1) - n + 1);
			n*(2*n*n - 3*n + 1);
			n*(2*n*n - 3*n + 1);
		}
		calc == {
			2*n*n + n;
			(2*n + 1)*n;
		}
		calc == {
			(2*n + 1)*n + (2*n + 1);
			(2*n + 1)*(n+1);
		}
		calc == {
			n*((n-1)*(2*n - 1)) + 6*n*n;
			n*(2*n*(n-1) - n + 1) + 6*n*n;
			n*(2*n*(n-1) - n + 1) + 6*n*n;
			n*(2*n*n - 3*n + 1) + 6*n*n;
			n*(2*n*n - 3*n + 1 + 6*n);
			n*(2*n*n + 6*n - 3*n + 1);
			n*(2*n*n + 3*n + 1);
			n*(2*n*n + n + (2*n + 1));
			n*((2*n + 1)*n + (2*n + 1));
		  	n*((2*n + 1)*(n+1));
		}
	}
}

*/

//ATOM_PLACEHOLDER_DivMod1

//ATOM_PLACEHOLDER_Main





