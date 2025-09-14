

// <vc-helpers>
function abs(x: int, y: int): nat {
    if x < y then y - x else x - y
}

lemma AbsCommutative(x: int, y: int)
    ensures abs(x, y) == abs(y, x)
{
}

lemma MinDistanceProperty(a: array<int>, b: array<int>, i: nat, j: nat, d: nat)
    requires a.Length != 0 && b.Length != 0
    requires 0 <= i < a.Length && 0 <= j < b.Length
    requires forall i',j' :: 0<=i'<j'<a.Length ==> a[i']<=a[j']
    requires forall i',j' :: 0<=i'<j'<b.Length ==> b[i']<=b[j']
    requires d == abs(a[i], b[j])
    requires forall i',j' :: 0<=i'<=i && 0<=j'<=j ==> d <= abs(a[i'], b[j'])
    ensures exists i',j':: 0<=i'<a.Length && 0<=j'<b.Length && d == abs(a[i'], b[j'])
{
}
// </vc-helpers>

// <vc-spec>
method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var j := 0;
    d := abs(a[0], b[0]);
    
    while i < a.Length && j < b.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= j <= b.Length
        invariant i < a.Length || j < b.Length
        invariant exists i',j':: 0<=i'<a.Length && 0<=j'<b.Length && d == abs(a[i'], b[j'])
        invariant forall i',j' :: 0<=i'<i && 0<=j'<b.Length ==> d <= abs(a[i'], b[j'])
        invariant forall i',j' :: 0<=i'<a.Length && 0<=j'<j ==> d <= abs(a[i'], b[j'])
    {
        var curr := abs(a[i], b[j]);
        if curr < d {
            d := curr;
        }
        
        if i == a.Length - 1 {
            j := j + 1;
        } else if j == b.Length - 1 {
            i := i + 1;
        } else if a[i] < b[j] {
            i := i + 1;
        } else {
            j := j + 1;
        }
    }
}
// </vc-code>

