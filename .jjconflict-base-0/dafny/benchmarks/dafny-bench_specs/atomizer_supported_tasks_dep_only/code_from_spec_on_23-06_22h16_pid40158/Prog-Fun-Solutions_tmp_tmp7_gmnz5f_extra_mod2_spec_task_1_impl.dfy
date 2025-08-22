// ATOM 

ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

// IMPL 

method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
{
    if n == 0 {
        a := 0;
    } else {
        var recursive_result := mod2(n/3);
        a := 5 * recursive_result + n % 4;
    }
}