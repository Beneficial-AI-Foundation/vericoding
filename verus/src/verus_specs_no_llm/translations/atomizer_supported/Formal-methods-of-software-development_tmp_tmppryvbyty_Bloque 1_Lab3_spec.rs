// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn factorial(n: int) -> int
    requires
        n>=0
{
    0
}

spec fn spec_multipleReturns(x: int, y: int) -> more:int, less:int)
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
method ComputeFact (n:int) returns (f:int
    requires
        y > 0,
        y > 0,
        y > 0,
        n>=0,
        n >=0
    ensures
        less < x < more
// SPEC 


method multipleReturns2 (x:int, y:int) returns (more:int, less:int),
        more + less == 2*x
// SPEC 

// TODO: Hacer en casa
method multipleReturns3 (x:int, y:int) returns (more:int, less:int),
        more - less == 2*y
// ATOM 

function factorial(n:int):int,
        f== factorial(n)
;

proof fn lemma_multipleReturns(x: int, y: int) -> (more: int, less: int)
requires y > 0
ensures less < x < more
// SPEC 


method multipleReturns2 (x:int, y: int) returns (more:int, less: int)
requires y > 0
ensures more + less == 2*x
// SPEC 

// TODO: Hacer en casa
method multipleReturns3 (x:int, y: int) returns (more:int, less: int)
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
    requires
        y > 0,
        y > 0,
        y > 0,
        n>=0,
        n >=0
    ensures
        less < x < more
// SPEC 


method multipleReturns2 (x:int, y:int) returns (more:int, less:int),
        more + less == 2*x
// SPEC 

// TODO: Hacer en casa
method multipleReturns3 (x:int, y:int) returns (more:int, less:int),
        more - less == 2*y
// ATOM 

function factorial(n:int):int,
        f== factorial(n)
{
    (0, 0, 0, 0, 0, 0)
}

}