// ATOM 
ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

// IMPL 
method mod(n:nat) returns (a:nat) 
ensures a == f(n)
{
    if n == 0 {
        a := 1;
    } else if n % 2 == 0 {
        var temp := mod(n / 2);
        a := 1 + 2 * temp;
    } else {
        var temp := mod(n / 2);
        a := 2 * temp;
    }
}