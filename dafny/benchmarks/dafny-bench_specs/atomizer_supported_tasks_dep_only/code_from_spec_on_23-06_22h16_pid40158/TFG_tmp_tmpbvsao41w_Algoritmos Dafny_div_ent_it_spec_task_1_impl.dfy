// IMPL 
method div_ent_it(a: int, b: int) returns (c: int, r: int)

// Algoritmo iterativo de la división de enteros
// que calcula su cociente y resto

    requires a >= 0 && b > 0
    ensures  a == b*c + r && 0 <= r < b
{
    c := 0;
    r := a;
    
    while r >= b
        invariant a == b*c + r
        invariant r >= 0
        decreases r
    {
        c := c + 1;
        r := r - b;
    }
}


//ATOM_PLACEHOLDER_Main