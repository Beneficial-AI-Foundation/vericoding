//IMPL Deli
method Deli(a: array<char>, i: nat)
modifies a
requires a.Length > 0
requires 0 <= i < a.Length
ensures forall j :: 0 <= j < i ==> a[j] == old(a[j])
ensures forall j :: i <= j < a.Length - 1 ==> a[j] == old(a[j + 1])
ensures a[a.Length - 1] == '.'
{
    var k := i;
    while k < a.Length - 1
        invariant i <= k < a.Length
        invariant forall j :: 0 <= j < i ==> a[j] == old(a[j])
        invariant forall j :: i <= j < k ==> a[j] == old(a[j + 1])
        invariant forall j :: k <= j < a.Length ==> a[j] == old(a[j])
    {
        a[k] := a[k + 1];
        k := k + 1;
    }
    a[a.Length - 1] := '.';
}

//IMPL DeliChecker
method DeliChecker()
{
    var a := new char[5];
    a[0] := 'a';
    a[1] := 'b';
    a[2] := 'c';
    a[3] := 'd';
    a[4] := 'e';
    
    Deli(a, 2);
    
    assert a[0] == 'a';
    assert a[1] == 'b';
    assert a[2] == 'd';
    assert a[3] == 'e';
    assert a[4] == '.';
}