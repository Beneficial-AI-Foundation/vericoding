// SPEC 
method factImp(n: int) returns (r: int)
{
}


// ATOM 

function power(n: int, m: nat) : int {
  if m==0 then 1 else n*power(n,m-1)
}


// ATOM 

function pow(n: int, m: nat,r: int) : int {
  if m==0 then r else pow(n,m-1,r*n)
}


// ATOM 

function powerAlt(n: int,m: nat) : int {
  pow(n,m,1)
}


// 3

// ATOM 

// 3

function equivalentes(n: int,m: nat,r: int) : int
  ensures power(n,m) == pow(n,m,r)
// ATOM 

lemma l1(n: int,m: nat, r: int)
  ensures equivalentes(n,m, r) == powerAlt(n,m)
// ATOM 


// 4.

function fact(n: nat) : nat
{
  if n==0 then 1 else n*fact(n-1)
}


// ATOM 

function factAcc(n: nat,a: int) : int
{
  if (n == 0) then a else factAcc(n-1,n*a)
}


// ATOM 

function factAlt(n: nat) : int { factAcc(n,1) }


// ATOM 

lemma factAcc_correct(n: nat,a: int)
  ensures factAcc(n,a) == fact(n)*a
// ATOM 

lemma equiv(n: nat)
  ensures fact(n) == factAlt(n) {
  factAcc_correct(n, 1);
}


// 5. a)
// ATOM 

// 5. a)
function mystery1(n: nat,m: nat) : nat
  ensures mystery1(n,m) == n+m
{ if n==0 then m else mystery1(n-1,m+1) }



// 5. b)
// ATOM 


// 5. b)
function mystery2(n: nat,m: nat) : nat
  ensures mystery2(n,m) == n+m
{ if m==0 then n else mystery2(n+1,m-1) }


// 5. c)
// ATOM 

// 5. c)
function mystery3(n: nat,m: nat) : nat
  ensures mystery3(n,m) == n*m
{ if n==0 then 0 else mystery1(m,mystery3(n-1,m)) }


// 5. d)
// ATOM 

// 5. d)
function mystery4(n: nat,m: nat) : nat
  ensures mystery4(n,m) == power(n,m)
{ if m==0 then 1 else mystery3(n,mystery4(n,m-1)) }


// 6

// 8

// 9

// 10

// 11


// 6

// 8

// 9

// 10

// 11
