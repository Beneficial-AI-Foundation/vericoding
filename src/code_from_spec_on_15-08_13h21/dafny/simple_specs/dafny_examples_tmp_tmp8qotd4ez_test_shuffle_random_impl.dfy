//IMPL 
method random(a: int, b: int) returns (r: int)
// requires a <= b
 ensures a <= b ==> a <= r <= b
{
    if a <= b {
        r := a;
    } else {
        r := 0; // arbitrary value when a > b since postcondition doesn't constrain this case
    }
}