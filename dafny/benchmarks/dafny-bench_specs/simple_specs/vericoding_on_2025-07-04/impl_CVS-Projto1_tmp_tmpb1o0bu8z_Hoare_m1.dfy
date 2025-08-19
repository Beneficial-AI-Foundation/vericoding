//ATOM
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//IMPL 
method m1 (x: int, y: int) returns (z: int)
requires 0 < x < y
ensures z >= 0 && z <= y && z != x
{
    z := 0;
}