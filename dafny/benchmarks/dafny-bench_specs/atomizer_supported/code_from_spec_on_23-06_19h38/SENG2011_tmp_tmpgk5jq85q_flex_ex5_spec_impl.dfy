//IMPL firste
method firste(a: array<char>) returns (c:int)
ensures -1 <= c < a.Length
ensures 0 <= c < a.Length ==> a[c] == 'e' && forall x :: 0 <= x < c ==> a[x] != 'e'
ensures c == -1 ==> forall x :: 0 <= x < a.Length ==> a[x] != 'e'
{
    c := 0;
    while c < a.Length
        invariant 0 <= c <= a.Length
        invariant forall x :: 0 <= x < c ==> a[x] != 'e'
    {
        if a[c] == 'e' {
            return;
        }
        c := c + 1;
    }
    c := -1;
}

//IMPL Main
method Main(){
}