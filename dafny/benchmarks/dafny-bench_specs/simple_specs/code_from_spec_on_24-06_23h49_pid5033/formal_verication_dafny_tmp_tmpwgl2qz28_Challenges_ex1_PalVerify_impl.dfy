//IMPL 
// ex3errors.dfy in Assignment 1
// verify that an array of characters is a Palindrome

method PalVerify(a: array<char>) returns (yn: bool)
ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j]) 
{
    var i := 0;
    while i < a.Length / 2
        invariant 0 <= i <= a.Length / 2
        invariant forall k :: 0 <= k < i ==> a[k] == a[a.Length - k - 1]
    {
        if a[i] != a[a.Length - i - 1] {
            yn := false;
            return;
        }
        i := i + 1;
    }
    yn := true;
}