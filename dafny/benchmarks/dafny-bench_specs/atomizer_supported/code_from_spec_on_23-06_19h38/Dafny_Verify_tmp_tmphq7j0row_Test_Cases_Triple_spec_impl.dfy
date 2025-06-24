// IMPL 
method Triple(x: int) returns (r: int)
{
    r := 3 * x;
}


// IMPL 
method TripleIf(x: int) returns (r: int) {
    if x >= 0 {
        r := 3 * x;
    } else {
        r := 3 * x;
    }
}


// IMPL 
method TripleOver(x: int) returns (r: int) {
    var i := 0;
    r := 0;
    while i < 3 {
        r := r + x;
        i := i + 1;
    }
}


// IMPL 
method TripleConditions(x: int) returns (r: int) 
requires x % 2 == 0
ensures r == 3 * x
{
    r := 3 * x;
}


// IMPL 
method Caller() {
    var result := Triple(5);
}