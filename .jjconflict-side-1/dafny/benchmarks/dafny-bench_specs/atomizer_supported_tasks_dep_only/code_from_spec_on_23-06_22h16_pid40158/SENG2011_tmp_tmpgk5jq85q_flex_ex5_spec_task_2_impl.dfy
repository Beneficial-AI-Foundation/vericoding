//IMPL firste
method firste(a: array<char>) returns (c:int)
ensures -1 <= c < a.Length
ensures 0 <= c < a.Length ==> a[c] == 'e' && forall x :: 0 <= x < c ==> a[x] != 'e'
ensures c == -1 ==> forall x :: 0 <= x < a.Length ==> a[x] != 'e'
{
    c := -1;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant c == -1
        invariant forall x :: 0 <= x < i ==> a[x] != 'e'
    {
        if a[i] == 'e' {
            c := i;
            return;
        }
        i := i + 1;
    }
}

//IMPL Main
method Main(){
}