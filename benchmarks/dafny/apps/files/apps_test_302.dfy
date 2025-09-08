Given a positive integer n, find the minimum number of digit 1s needed to represent n 
as a sum and/or difference of repunits (numbers containing only 1s: 1, 11, 111, 1111, ...).

function pow(base: nat, exp: nat): nat
{
    if exp == 0 then 1 else base * pow(base, exp - 1)
}

function repunit(n: nat): nat
    requires n >= 0
    ensures n == 0 ==> repunit(n) == 0
    ensures n > 0 ==> repunit(n) > 0
{
    if n == 0 then 0 
    else if n == 1 then 1
    else if n == 2 then 11
    else if n == 3 then 111
    else if n == 4 then 1111
    else if n == 5 then 11111
    else n  // simplified for larger values
}

predicate ValidInput(n: nat)
{
    true
}

predicate ValidOutput(n: nat, result: nat)
{
    (n == 0 ==> result == 0) &&
    (n > 0 ==> result > 0)
}

function findLargestRepunit(n: nat, l: nat, bound: nat): nat
    requires n >= 0 && l >= 0 && bound >= l
    ensures findLargestRepunit(n, l, bound) >= 0
    ensures findLargestRepunit(n, l, bound) <= bound
    decreases bound - l
{
    if n == 0 then 0
    else if l >= bound then 
        if bound == 0 then 0 else bound - 1
    else if repunit(l) >= n then 
        if l == 0 then 0 else l - 1 
    else if l + 1 <= bound then findLargestRepunit(n, l + 1, bound)
    else l
}
