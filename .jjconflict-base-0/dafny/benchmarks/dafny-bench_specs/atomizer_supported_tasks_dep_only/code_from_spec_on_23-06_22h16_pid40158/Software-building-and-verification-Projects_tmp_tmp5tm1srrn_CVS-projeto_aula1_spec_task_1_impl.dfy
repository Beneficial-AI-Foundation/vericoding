//IMPL factImp
/* code modified by LLM (iteration 4): fixed loop invariant to correctly track factorial value */
method factImp(n: int) returns (r: int)
    requires n >= 0
    ensures r == fact(n)
{
    if n == 0 {
        r := 1;
    } else {
        r := 1;
        var i := 1;
        /* code modified by LLM (iteration 4): corrected loop invariant to match actual computation */
        while i <= n
            invariant 1 <= i <= n + 1
            invariant r == fact(i - 1)
            decreases n - i + 1
        {
            /* code modified by LLM (iteration 4): multiply r by i, then increment i */
            r := r * i;
            i := i + 1;
        }
    }
}

//ATOM power
function power(base: int, exp: nat): int
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}

//ATOM pow
function pow(base: int, exp: nat): int
{
    power(base, exp)
}

//ATOM powerAlt
function powerAlt(base: int, exp: nat): int
{
    if exp == 0 then 1
    else if exp % 2 == 0 then
        var half := powerAlt(base, exp / 2);
        half * half
    else
        base * powerAlt(base, exp - 1)
}

//ATOM equivalentes
lemma equivalentes(base: int, exp: nat)
    ensures power(base, exp) == powerAlt(base, exp)
{
    // Proof by induction would go here
}

//ATOM l1
lemma l1(base: int, exp: nat)
    ensures power(base, exp) == powerAlt(base, exp)
{
    equivalentes(base, exp);
}

//ATOM fact
function fact(n: nat): nat
{
    if n == 0 then 1
    else n * fact(n - 1)
}

//ATOM factAcc
function factAcc(n: nat, acc: nat): nat
{
    if n == 0 then acc
    else factAcc(n - 1, n * acc)
}

//ATOM factAlt
function factAlt(n: nat): nat
{
    factAcc(n, 1)
}

//ATOM factAcc_correct
lemma factAcc_correct(n: nat, acc: nat)
    ensures factAcc(n, acc) == fact(n) * acc
{
    // Proof by induction would go here
}

//ATOM equiv
lemma equiv(n: nat)
    ensures fact(n) == factAlt(n)
{
    factAcc_correct(n, 1);
}

//ATOM mystery1
function mystery1(n: nat): nat
{
    if n == 0 then 0
    else n + mystery1(n - 1)
}

//ATOM mystery2
function mystery2(n: nat): nat
{
    if n == 0 then 1
    else 2 * mystery2(n - 1)
}

//ATOM mystery3
function mystery3(n: nat): nat
{
    if n <= 1 then n
    else mystery3(n - 1) + mystery3(n - 2)
}

//ATOM mystery4
function mystery4(n: nat, m: nat): nat
{
    if n == 0 then m
    else mystery4(n - 1, m + 1)
}