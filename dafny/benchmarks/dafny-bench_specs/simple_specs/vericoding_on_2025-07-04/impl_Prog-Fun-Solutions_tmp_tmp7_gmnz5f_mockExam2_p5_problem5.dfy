//ATOM
// problem 5:
// name:   Gabriele Berardi
// s-number: s4878728
// table:   XXXX

ghost function f(n: int): int {
 if n < 0 then 0 else 3*f(n-5) + n
}

//IMPL problem5
method problem5(n:nat) returns (x: int)
ensures x == f(n)
{
    if n < 5 {
        x := n;
    } else {
        var temp := problem5(n - 5);
        x := 3 * temp + n;
    }
}