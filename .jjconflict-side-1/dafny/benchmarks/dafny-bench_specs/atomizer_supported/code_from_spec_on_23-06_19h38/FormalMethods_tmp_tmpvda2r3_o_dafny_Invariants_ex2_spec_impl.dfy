// ATOM 
function Potencia(x:nat, y:nat):nat
{
    if y == 0
    then 1
    else x * Potencia(x, y-1)
}

//IMPL 
method Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x,y)
{
    var b := x;
    var e := y;
    r := 1;
    
    while e > 0
        invariant Potencia(b, e) * r == Potencia(x, y)
        decreases e
    {
        r := r * b;
        e := e - 1;
    }
}