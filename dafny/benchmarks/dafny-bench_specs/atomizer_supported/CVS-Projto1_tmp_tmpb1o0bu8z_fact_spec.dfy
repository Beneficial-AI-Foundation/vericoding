// ATOM 
function fact (n:nat): nat
{if n == 0 then 1 else n * fact(n-1)}


// ATOM 

function factAcc (n:nat, a:int): int
{if (n==0) then a else factAcc(n-1,n*a)}


// ATOM 

function factAlt(n:nat):int
{factAcc(n,1)}


// ATOM 

lemma factAcc_correct (n:nat, a:int)
 ensures factAcc(n, a) == a*fact(n)
{
}


// ATOM 

lemma factAlt_correct (n:nat)
 ensures factAlt(n) == fact(n)
{
    factAcc_correct(n,1);
}


// ATOM 

datatype List<T> = Nil | Cons(T, List<T>)
// ATOM 

function length<T> (l: List<T>) : nat
{
    match l
    case Nil => 0
    case Cons(_, r) => 1 + length(r)
}


 length_non_neg<T> (l:List<T>)
    ensures length(l) >= 0
{
    match l
    case Nil =>
    case Cons(_, r) =>
        length_non_neg(r);
       //  assert forall k : int :: k >= 0 ==> 1 + k >= 0;
}

// ATOM 

function lengthTL<T> (l: List<T>, acc: nat) : nat
{
    match l
    case Nil => acc
    case Cons(_, r) => lengthTL(r, 1 + acc)
}

lengthTL_aux<T> (l: List<T>, acc: nat)
    ensures lengthTL(l, acc) == acc + length(l)
{
    match l
    case Nil => assert acc + length<T>(Nil) == acc;
    case Cons(_, r) =>
        lengthTL_aux(r, acc + 1);
}
// ATOM 
lemma lengthEq<T> (l: List<T>)
    ensures length(l) == lengthTL(l,0)
{
    lengthTL_aux(l, 0);
}




